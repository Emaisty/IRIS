#!/usr/bin/env python3
"""Reproducible isolated audit checks; no project sources or existing caches changed.

Usage: python3 validate.py prepare|patched|official|summarize
Environment: AUDIT_WORK (new directory), AUDIT_TOOLCHAINS (previous built checkers).
The checkers are hashed, not rebuilt here. Both project Java extensions are rebuilt.
"""
import concurrent.futures
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import time

EVIDENCE = Path(__file__).resolve().parent
ROOT = EVIDENCE.parent.parent
WORK = Path(os.environ.get('AUDIT_WORK', '/private/tmp/iris-semantic-audit-20261001'))
TOOLS = Path(os.environ.get('AUDIT_TOOLCHAINS', '/private/tmp/iris-arend-20260930'))
JDK = TOOLS / 'jdk25/jdk-25.0.4.1+1/Contents/Home'
PIN = 'b9b6cf04478a3088aef800497cdd275d2bce0967'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def output(*args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.STDOUT)


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')


def prepare():
    WORK.mkdir()  # fail rather than reuse old caches
    sources = sorted([ROOT / 'arend.yaml', *ROOT.glob('src/**/*.ard'),
                      *ROOT.glob('proofmode-extension/**/*.java'), *ROOT.glob('scripts/*.sh')])
    manifest = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    save(EVIDENCE / 'source-manifest.json', manifest)
    state = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'iris_head': output('git', 'rev-parse', 'HEAD').strip(),
             'status': output('git', 'status', '--porcelain=v1'),
             'worktree_diff_sha256': hashlib.sha256(output('git', 'diff', '--binary').encode()).hexdigest(),
             'index_diff_sha256': hashlib.sha256(output('git', 'diff', '--cached', '--binary').encode()).hexdigest(),
             'tracked_file_hashes': {p: sha(ROOT / p) for p in output('git', 'ls-files').splitlines()
                                    if (ROOT / p).is_file()},
             'reference_pin': PIN,
             'reference_local_head': output('git', 'rev-parse', 'HEAD', cwd=ROOT / 'support_files/iris').strip(),
             'reference_local_status': output('git', 'status', '--porcelain=v1', cwd=ROOT / 'support_files/iris'),
             'reference_local_diff': output('git', 'diff', '--stat', PIN, 'HEAD', cwd=ROOT / 'support_files/iris'),
             'java': output(str(JDK / 'bin/java'), '-version'),
             'javac': output(str(JDK / 'bin/javac'), '-version'),
             'python': sys.version,
             'work': str(WORK), 'toolchains': {}}
    archive = WORK / 'reference.tar'
    with archive.open('wb') as f:
        subprocess.run(['git', 'archive', PIN], cwd=ROOT / 'support_files/iris', stdout=f, check=True)
    reference = WORK / 'reference'
    reference.mkdir()
    with tarfile.open(archive) as tar:
        for entry in tar.getmembers():
            if entry.name.startswith('/') or '..' in Path(entry.name).parts or entry.issym() or entry.islnk():
                raise ValueError('Unexpected archive member: ' + entry.name)
        tar.extractall(reference)
    state['reference_archive_sha256'] = sha(archive)
    save(EVIDENCE / 'reference-manifest.json', {
        str(p.relative_to(reference)): sha(p) for p in sorted(reference.rglob('*')) if p.is_file()})
    for variant in ['official', 'patched']:
        origin = TOOLS / variant
        dest = WORK / variant
        project = dest / 'IRIS'
        project.mkdir(parents=True)
        for name in ['src', 'proofmode-extension', 'scripts']:
            shutil.copytree(ROOT / name, project / name)
        shutil.copy2(ROOT / 'arend.yaml', project / 'arend.yaml')
        lib = dest / 'libs/arend-lib'
        lib.mkdir(parents=True)
        for name in ['src', 'ext']:
            shutil.copytree(origin / 'arend-lib' / name, lib / name)
        shutil.copy2(origin / 'arend-lib/arend.yaml', lib / 'arend.yaml')
        jar = origin / 'cli/build/libs/cli-1.12.0-full.jar'
        state['toolchains'][variant] = {
            'head': output('git', 'rev-parse', 'HEAD', cwd=origin).strip(),
            'status': output('git', 'status', '--porcelain=v1', cwd=origin),
            'jar': str(jar), 'jar_sha256': sha(jar),
            'stdlib_tree': output('git', 'rev-parse', 'HEAD:arend-lib', cwd=origin).strip(),
            'stdlib_inputs': {str(p.relative_to(lib)): sha(p) for p in sorted(lib.rglob('*')) if p.is_file()},
            'initial_project_bin_exists': (project / 'bin').exists(),
            'initial_stdlib_bin_exists': (lib / 'bin').exists()}
        env = dict(os.environ, JAVA_HOME=str(JDK), PATH=str(JDK / 'bin') + ':' + os.environ['PATH'], AREND_JAR=str(jar))
        cmd = ['bash', str(project / 'scripts/build-proofmode-extension.sh')]
        res = subprocess.run(cmd, cwd=project, env=env, capture_output=True, text=True)
        (EVIDENCE / f'{variant}-extension-build.log').write_text(res.stdout + res.stderr)
        state['toolchains'][variant]['extension_build'] = {
            'command': cmd, 'exit_code': res.returncode,
            'outputs': {str(p.relative_to(project)): sha(p) for p in sorted((project / 'ext').rglob('*.class'))}}
        if res.returncode:
            save(EVIDENCE / 'environment.json', state)
            raise SystemExit('Extension build failed: ' + variant)
    old = json.loads((ROOT / 'docs/typecheck-evidence/source-manifest.json').read_text())
    state['previous_source_manifest_comparison'] = {
        'matched': [p for p in manifest if p in old and manifest[p] == old[p]],
        'changed': [p for p in manifest if p in old and manifest[p] != old[p]],
        'new': [p for p in manifest if p not in old]}
    save(EVIDENCE / 'environment.json', state)
    print('Prepared', WORK, 'with', len(manifest), 'inputs', flush=True)


def run(variant, label, args, deadline):
    project = WORK / variant / 'IRIS'
    logdir = EVIDENCE / 'validation' / variant
    logdir.mkdir(parents=True, exist_ok=True)
    cmd = [str(JDK / 'bin/java'), '-Xmx8g', '-Xss16m', '-jar',
           str(TOOLS / variant / 'cli/build/libs/cli-1.12.0-full.jar'),
           '-L', str(WORK / variant / 'libs'), *args]
    record = {'command': cmd, 'cwd': str(project), 'deadline_seconds': deadline,
              'source_recompile': '-r' in args,
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    start = time.monotonic()
    with (logdir / (label + '.log')).open('w') as f:
        proc = subprocess.Popen(cmd, cwd=project, stdout=f, stderr=subprocess.STDOUT, start_new_session=True)
        save(logdir / (label + '.running.json'), {**record, 'pid': proc.pid})
        try:
            code = proc.wait(timeout=deadline)
            record['timed_out'] = False
        except subprocess.TimeoutExpired:
            record['timed_out'] = True
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                code = proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                code = proc.wait()
    text = (logdir / (label + '.log')).read_text(errors='replace')
    record.update(exit_code=code, elapsed_seconds=round(time.monotonic() - start, 3),
                  errors=len(re.findall(r'\[ERROR\]', text)), goals=len(re.findall(r'\[GOAL\]', text)),
                  completion_markers=len(re.findall(r'--- Done \(', text)),
                  crash=bool(re.search(r'Exception in thread|OutOfMemoryError|StackOverflowError|fatal error', text)))
    record['status'] = ('timeout' if record['timed_out'] else 'crash' if record['crash'] else
                        'error' if record['errors'] else 'goals' if record['goals'] else
                        'incomplete' if code != 0 or not record['completion_markers'] else 'pass')
    save(logdir / (label + '.json'), record)
    (logdir / (label + '.running.json')).unlink()
    print(variant, label, record['status'], record['elapsed_seconds'], flush=True)
    return record


def official():
    sources = WORK / 'official/IRIS/src'
    modules = {'.'.join(p.relative_to(sources).with_suffix('').parts): p for p in sorted(sources.rglob('*.ard'))}
    order, seen = [], set()
    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for dep in sorted(set(re.findall(r'^\\import\s+([\w.]+)', modules[m].read_text(), re.M)) & modules.keys()):
            visit(dep)
        order.append(m)
    for m in modules:
        visit(m)
    save(EVIDENCE / 'dependency-order.json', order)
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        futures = {pool.submit(run, 'official', m, ['-r', m], 120): m for m in order}
        for future in concurrent.futures.as_completed(futures):
            future.result()


def summarize():
    results = {}
    for variant in ['official', 'patched']:
        results[variant] = {p.stem: json.loads(p.read_text()) for p in sorted((EVIDENCE / 'validation' / variant).glob('*.json'))
                            if not p.name.endswith('.running.json')}
    save(EVIDENCE / 'validation-summary.json', results)
    before = json.loads((EVIDENCE / 'source-manifest.json').read_text())
    state = json.loads((EVIDENCE / 'environment.json').read_text())
    preservation = {'source_changes': [p for p, h in before.items() if sha(ROOT / p) != h],
                    'preexisting_tracked_changes': [p for p, h in state['tracked_file_hashes'].items() if sha(ROOT / p) != h],
                    'final_status': output('git', 'status', '--porcelain=v1')}
    save(EVIDENCE / 'preservation.json', preservation)
    print({v: {s: sum(r['status'] == s for r in rs.values()) for s in ['pass', 'error', 'goals', 'crash', 'timeout', 'incomplete']}
           for v, rs in results.items()})


if __name__ == '__main__':
    action = sys.argv[1]
    if action == 'prepare':
        prepare()
    elif action == 'patched':
        run('patched', 'full-source', ['-r', '--serialize', '--show-times'], 2400)
    elif action == 'official':
        official()
    elif action == 'summarize':
        summarize()
    else:
        raise SystemExit('Unknown action: ' + action)
