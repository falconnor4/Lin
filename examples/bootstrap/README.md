# Bootstrap

An implementation of the Lin core written in Lin. It follows the same pipeline as
the C engine, and serves as an executable description of it and as a stress test
of the language.

```
source text or tokens
   │  parse.lin
   ▼
term
   │  compile.lin
   ▼
interaction net
   │  reduce.lin, net.lin
   ▼
reduced net
   │  readback.lin
   ▼
term
```

## Modules

| File | Contents |
|------|----------|
| `types.lin` | The datatypes: node tags, ports, nodes, redexes, terms, and the net |
| `net.lin` | The net as a node table: linking wires, finding redexes, and the rewrite rules |
| `reduce.lin` | The reduction loop |
| `compile.lin` | Term to net: scoping, counting variable uses, building duplication trees |
| `readback.lin` | Net to term, and term equality |
| `parse.lin` | Tokens to terms |
| `read.lin`, `read_text.lin` | Source text to tokens |
| `front.lin` | The reader and printer used by the stand-alone entry point |
| `lin.lin` | Entry points: `eval_term`, `eval_tokens`, `eval_str`, `eval_num` |
| `boot.lin` | A stand-alone entry point that reads a source file |
| `test_bootstrap.lin` | The test program |

## Running

```bash
./lin examples/bootstrap/test_bootstrap.lin
```

The test program compiles, reduces and reads back a set of terms through the
bootstrapped pipeline and prints `=> true` when every result matches.

`bin/lin-boot FILE.lin` runs `boot.lin` on a source file. The stand-alone front
end is work in progress: it reads and prints the first form of the file.

## Status

The bootstrapped core covers the five node tags and the full rule set. It does not
yet replace the C engine: the reader is incomplete, and running the bootstrapped
reducer on large programs is slow. `test/bootstrap_gate.py` tracks the language
features the self-hosted front end still needs.
