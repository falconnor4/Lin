// web/run.mjs: run a Lin program on the WebAssembly build, from node -- how the web build is tested.
//   node web/run.mjs <dist-dir> <file.lin> [more lin arguments]
// The program (and any file it loads by a relative path) is copied into the module's file system.
import { readFileSync, existsSync } from 'node:fs';
import { resolve, dirname, relative } from 'node:path';
import { pathToFileURL } from 'node:url';
const [dist, file, ...rest] = process.argv.slice(2);
if (!dist || !file) { console.error('usage: node web/run.mjs <dist-dir> <file.lin> [args]'); process.exit(2); }
const createLin = (await import(pathToFileURL(resolve(dist, 'lin.js')).href)).default;
const lin = await createLin({ print: (s) => process.stdout.write(s + '\n'), printErr: (s) => process.stderr.write(s + '\n'), locateFile: (p) => resolve(dist, p),
  // (the engine's settings, LIN_*, from this process's environment: a module has an environment of its own)
  preRun: [(m) => { for (const [k, v] of Object.entries(process.env)) if (k.startsWith('LIN_')) m.ENV[k] = v; }] });
// the program at the same relative path, and the files beside it (a `(load "x.lin")` of a neighbour)
const rel = relative(process.cwd(), resolve(file)), dir = dirname(rel);
const mk = (d) => { let p = ''; for (const part of d.split('/')) { if (!part || part === '.') continue; p += '/' + part; try { lin.FS.mkdir(p); } catch {} } };
mk(dir);
lin.FS.writeFile('/' + rel, readFileSync(file));
lin.FS.chdir('/');
let code = 0;
try { code = lin.callMain([...rest, rel]); } catch (e) { if (e && e.name === 'ExitStatus') code = e.status; else { process.stderr.write(String(e && e.stack || e) + '\n'); code = 1; } }
process.exit(code || 0);
