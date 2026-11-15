#!/usr/bin/env bash
# Input arrives as a list: what `io_file` hands a program is a value of the core's list datatype, built by the
# readback driver -- its cells, and an end that must reduce to `nil` when read (it carries its constructor's
# marker, a redex).  Nothing else in the suite reads input, so this checks it: length, the end, a `match` on it, the
# library's string functions -- compiled and on the net alone.
set -u
LIN_BIN="${1:-./lin}"
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
printf 'the quick  brown fox' > "$TMP/in.txt"
cat > "$TMP/p.lin" <<LIN
(io_file "$TMP/in.txt" (\\s (io_print (str_length s) (io_print "\\n"
  (io_print (if (list.is_empty (str_drop 20 s)) 1 0) (io_print "\\n"
  (io_print (match (str_drop 19 s) ((list.cons c rest) (add c (match rest ((list.cons d _) 1000) (list.nil 0)))) (list.nil 7)) (io_print "\\n"
  (io_print (slength (str_words s)) (io_print "\\n"
  (io_print (str_reverse (str_take 3 s)) (io_print "\\n" 0))))))))))))
LIN
want=$(printf '20\n1\n120\n4\neht')
fail=0
for mode in compiled net; do
  if [ "$mode" = net ]; then got=$(LIN_FN_OFF=1 timeout 60 "$LIN_BIN" "$TMP/p.lin" 2>/dev/null | grep -v '^=>'); else got=$(timeout 60 "$LIN_BIN" "$TMP/p.lin" 2>/dev/null | grep -v '^=>'); fi
  if [ "$got" != "$want" ]; then echo "io_input: $mode: got '$got', want '$want'"; fail=1; fi
done
[ "$fail" = 0 ] && echo "io_input: OK (a file read with io_file is a list: length, end, match, words -- compiled and on the net)"
exit $fail
