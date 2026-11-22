#!/usr/bin/env node
'use strict';
/* =============================================================================
 * ci_guards.cjs - the three guards every The-Optimisers repo runs in CI, plus the NOT RUN floor.
 * Jennifer 2-Nov-2026: "we want all checks and to organise them all". Shared home: agency-os-agents.
 *
 *   G1 secret scan        a committed credential fails the build (fingerprint printed, never the value)
 *   G2 laptop-path ceiling lines naming this laptop (C:\Users, C:/Users, OneDrive - PS) may only go DOWN;
 *                         the ceiling lives in .ci/laptop_paths.ceiling (P5.9 of the organisation plan)
 *   G3 client-data guard  nothing listed in .ci/never_in_git.txt may be tracked by git. A line "!<exact path>" PINS one
 *                         file that was already tracked when CI arrived (Jennifer 9-Nov-2026: pre-existing reds land
 *                         pinned as a ratchet). It prints G3 PINNED, not a failure; a pin whose file is no longer
 *                         tracked fails, so the list can only shrink. Pins come from the repo's ci_matrix.json row
 *                         (neverInGit); a new tracked match is never pinned, it is untracked.
 *   F  NOT RUN floor      a check that could not run is NOT RUN, never a pass; --not-run-max caps how many
 *
 * RUN   node ci_guards.cjs [--repo <dir>] [--not-run <n>] [--not-run-max <n>]
 *       --not-run       checks the CALLER already declared NOT RUN (e.g. tests it had to exclude)
 *       --not-run-max   the repo's ceiling on NOT RUN (default 0)
 * EXIT  0 every guard passed and NOT RUN is within its ceiling; 1 a guard failed; 2 could not run
 * The last line is CI_GUARDS_JSON {...}. NO REGEX (house rule 2026-09-08). Needs git on PATH.
 * tools/ci_fleet_sync.cjs copies this file, byte for byte, to each repo's .ci/ci_guards.cjs (a reusable
 * workflow cannot read a sibling private repo on the free plan without a token); the fleet check fails on drift.
 * ============================================================================= */
const fs = require('fs'), path = require('path'), cp = require('child_process'), crypto = require('crypto');

const BUILD = 'CI-GUARDS-2026-11-09-r2';
const args = process.argv.slice(2);
function opt(name, dflt) { const i = args.indexOf(name); return i >= 0 && args[i + 1] !== undefined ? args[i + 1] : dflt; }
const repo = path.resolve(opt('--repo', process.cwd()));
const declaredNotRun = Number(opt('--not-run', '0')) || 0;
const notRunMax = Number(opt('--not-run-max', '0')) || 0;

const report = { build: BUILD, repo, guards: {}, notRun: declaredNotRun, notRunMax, verdict: '' };
function finish(code, verdict, reason) {
    report.verdict = verdict; report.reason = reason || ''; report.exit = code;
    console.log('');
    console.log('VERDICT: ' + verdict + (reason ? ' - ' + reason : ''));
    console.log('CI_GUARDS_JSON ' + JSON.stringify(report));
    process.exit(code);
}

let tracked;
try {
    tracked = cp.execFileSync('git', ['-C', repo, 'ls-files', '-z'], { encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 })
        .split('\0').filter(Boolean);
} catch (e) { finish(2, 'COULD-NOT-RUN', 'git ls-files failed: ' + (e.message || e)); }
if (tracked.length === 0) finish(2, 'COULD-NOT-RUN', 'git tracks no files here (wrong --repo, or not a checkout)');

const TEXT_MAX = 4 * 1024 * 1024;
function isBinary(buf) { const n = Math.min(buf.length, 8000); for (let i = 0; i < n; i++) if (buf[i] === 0) return true; return false; }
function readText(rel) {
    const p = path.join(repo, rel);
    let st; try { st = fs.statSync(p); } catch { return null; }
    if (!st.isFile() || st.size > TEXT_MAX) return null;
    const buf = fs.readFileSync(p);
    if (isBinary(buf)) return null;
    return buf.toString('utf8');
}
const ALNUM = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
const HEX = '0123456789abcdefABCDEF';
const TOK = ALNUM + '_-.';
function runOf(s, i, chars) { let j = i; while (j < s.length && chars.indexOf(s.charAt(j)) >= 0) j++; return j - i; }
function fp(s) { return crypto.createHash('sha256').update(s).digest('hex').slice(0, 12); }

/* ---- G1 secret scan: four detectors, the same families scan_credentials.ps1 covers ---- */
function scanLine(line) {
    const hits = [];
    // Airtable PAT: "pat" + 14 alnum + "." + 64 hex
    let k = 0;
    while ((k = line.indexOf('pat', k)) >= 0) {
        const a = runOf(line, k + 3, ALNUM);
        if (a === 14 && line.charAt(k + 17) === '.' && runOf(line, k + 18, HEX) === 64) hits.push({ kind: 'airtable-pat', fp: fp(line.substr(k, 82)) });
        k += 3;
    }
    // Pipedrive token in a URL: api_token= + 40 hex
    k = 0;
    while ((k = line.indexOf('api_token=', k)) >= 0) {
        if (runOf(line, k + 10, HEX) === 40) hits.push({ kind: 'pipedrive-token', fp: fp(line.substr(k + 10, 40)) });
        k += 10;
    }
    // A literal bearer token: "Bearer " + 32+ token chars that are not a placeholder ($, {, <)
    k = 0;
    while ((k = line.indexOf('Bearer ', k)) >= 0) {
        const c = line.charAt(k + 7);
        const n = runOf(line, k + 7, TOK);
        if (n >= 32 && '${<'.indexOf(c) < 0 && c !== '') hits.push({ kind: 'bearer-literal', fp: fp(line.substr(k + 7, n)) });
        k += 7;
    }
    return hits;
}
/* A private key BLOCK, not a mention of one: the BEGIN marker followed, before its END marker, by at
 * least 200 base64 characters. A fixture's 16-char stub or a comment naming the format is not a key
 * (SignoffWorker no_regex_equivalence.test.mjs and worker.js, 2-Nov: three false hits on the first cut). */
const B64 = ALNUM + '+/=';
function scanPem(text) {
    const hits = []; let k = 0;
    while ((k = text.indexOf('-----BEGIN ', k)) >= 0) {
        const head = text.indexOf('-----', k + 11);
        const label = head > 0 ? text.slice(k + 11, head) : '';
        k += 11;
        if (head < 0 || label.indexOf('PRIVATE KEY') < 0) continue;
        const end = text.indexOf('-----END ', head + 5);
        if (end < 0 || end - head > 12000) continue;                 // no closing marker: a mention, not a block
        // Drop layout (whitespace, a literal \n inside a string). What is left must be key material:
        // 200+ characters and 95%+ base64. Code that merely sits between two markers fails the ratio.
        const body = text.slice(head + 5, end).split('\\n').join('');
        let n = 0, other = 0;
        for (const ch of body) { if (' \t\r\n'.indexOf(ch) >= 0) continue; if (B64.indexOf(ch) >= 0) n++; else other++; }
        if (n >= 200 && other * 20 <= n) hits.push({ kind: 'pem-private-key', fp: fp(body), at: text.slice(0, k).split('\n').length });
    }
    return hits;
}
const SELF = path.basename(__filename);
{
    const findings = []; let scanned = 0;
    for (const rel of tracked) {
        if (rel.endsWith(SELF) || rel.endsWith('worker-ci.yml')) continue;   // the detectors describe themselves
        const text = readText(rel); if (text === null) continue;
        scanned++;
        const lines = text.split('\n');
        for (let i = 0; i < lines.length; i++) for (const h of scanLine(lines[i])) findings.push({ file: rel, line: i + 1, kind: h.kind, fp: h.fp });
        for (const h of scanPem(text)) findings.push({ file: rel, line: h.at, kind: h.kind, fp: h.fp });
    }
    report.guards.secretScan = { scanned, findings };
    for (const f of findings) console.log('G1 SECRET  ' + f.file + ':' + f.line + '  ' + f.kind + '  fp ' + f.fp);
    console.log('G1 secret scan: ' + scanned + ' text files, ' + findings.length + ' finding(s)');
}

/* ---- G2 laptop-path ceiling ---- */
{
    const needles = ['C:\\Users', 'C:/Users', 'OneDrive - PS'];
    let count = 0; const where = {};
    for (const rel of tracked) {
        if (rel === '.ci/laptop_paths.ceiling' || rel.endsWith(SELF)) continue;   // this file names the needles
        const text = readText(rel); if (text === null) continue;
        const lines = text.split('\n');
        for (const ln of lines) if (needles.some((n) => ln.indexOf(n) >= 0)) { count++; where[rel] = (where[rel] || 0) + 1; }
    }
    const ceilFile = path.join(repo, '.ci', 'laptop_paths.ceiling');
    let ceiling = null, raw = '';
    try { raw = fs.readFileSync(ceilFile, 'utf8').trim(); } catch { raw = ''; }
    if (raw !== '' && raw.split('').every((c) => '0123456789'.indexOf(c) >= 0)) ceiling = Number(raw);
    report.guards.laptopPaths = { count, ceiling, files: where };
    const top = Object.entries(where).sort((a, b) => b[1] - a[1]).slice(0, 10);
    for (const [f, n] of top) console.log('G2 PATH    ' + n + '  ' + f);
    console.log('G2 laptop paths: ' + count + ' line(s), ceiling ' + (ceiling === null ? 'MISSING (.ci/laptop_paths.ceiling)' : ceiling));
}

/* ---- G3 client-data guard ---- */
{
    const listFile = path.join(repo, '.ci', 'never_in_git.txt');
    let rules = null, pins = [];
    try {
        const lines = fs.readFileSync(listFile, 'utf8').split('\n').map((s) => s.trim()).filter((s) => s && s.charAt(0) !== '#');
        pins = lines.filter((s) => s.charAt(0) === '!').map((s) => s.slice(1).trim());
        rules = lines.filter((s) => s.charAt(0) !== '!');
    } catch { rules = null; }
    const matches = [], pinned = [];
    if (rules) {
        for (const rel of tracked) for (const r of rules) {
            const hit = r.endsWith('/') ? (rel.indexOf(r) === 0 || rel.indexOf('/' + r) >= 0)
                : r.charAt(0) === '*' ? rel.endsWith(r.slice(1))
                : (rel === r || rel.endsWith('/' + r));
            if (hit) { if (pins.indexOf(rel) >= 0) pinned.push({ file: rel, rule: r }); else matches.push({ file: rel, rule: r }); break; }
        }
    }
    const stalePins = pins.filter((p) => !pinned.some((m) => m.file === p));
    report.guards.clientData = { rules: rules ? rules.length : null, matches, pinned: pinned.map((m) => m.file), stalePins };
    for (const m of matches) console.log('G3 TRACKED ' + m.file + '  (rule ' + m.rule + ')');
    for (const m of pinned) console.log('G3 PINNED  ' + m.file + '  (rule ' + m.rule + '; pre-existing, pinned)');
    for (const p of stalePins) console.log('G3 STALE PIN ' + p + '  (no longer a tracked match: delete its "!" line from the ci_matrix.json row and re-sync, so the list can only shrink)');
    console.log('G3 client data: ' + (rules === null ? 'NOT RUN (.ci/never_in_git.txt missing)' : rules.length + ' rule(s), ' + matches.length + ' tracked match(es), ' + pinned.length + ' pinned'));
}

/* ---- verdict ---- */
const fails = [];
if (report.guards.secretScan.findings.length) fails.push('G1 ' + report.guards.secretScan.findings.length + ' secret(s)');
if (report.guards.laptopPaths.ceiling === null) fails.push('G2 no ceiling file');
else if (report.guards.laptopPaths.count > report.guards.laptopPaths.ceiling) fails.push('G2 ' + report.guards.laptopPaths.count + ' laptop-path lines over the ceiling of ' + report.guards.laptopPaths.ceiling);
if (report.guards.clientData.matches.length) fails.push('G3 ' + report.guards.clientData.matches.length + ' client-data file(s) tracked');
if (report.guards.clientData.stalePins && report.guards.clientData.stalePins.length) fails.push('G3 ' + report.guards.clientData.stalePins.length + ' stale pin(s): lower the list');
let notRun = declaredNotRun + (report.guards.clientData.rules === null ? 1 : 0);
report.notRun = notRun;
if (notRun > notRunMax) fails.push('NOT RUN ' + notRun + ' over the ceiling of ' + notRunMax);
if (report.guards.laptopPaths.ceiling !== null && report.guards.laptopPaths.count < report.guards.laptopPaths.ceiling)
    console.log('NOTE: laptop paths fell to ' + report.guards.laptopPaths.count + '; lower .ci/laptop_paths.ceiling to match so it cannot creep back');
if (fails.length) finish(1, 'FAIL', fails.join('; '));
finish(0, 'PASS', 'G1 clean, G2 ' + report.guards.laptopPaths.count + '/' + report.guards.laptopPaths.ceiling + ', G3 ' + report.guards.clientData.matches.length + ' tracked' + (report.guards.clientData.pinned.length ? ' (' + report.guards.clientData.pinned.length + ' pinned)' : '') + ', NOT RUN ' + notRun + '/' + notRunMax);
