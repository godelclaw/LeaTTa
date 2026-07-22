<!-- SPDX-License-Identifier: Apache-2.0 -->

# Upstream PeTTa patches (candidates for a PR to patham9/PeTTa)

## petta-string-escape-fix.patch
Two genuine string-handling bugs in native PeTTa, found while building a
verified model of it:
- `src/filereader.pl` (grab_until_balanced / strip): the form reader toggled
  in-string state on EVERY `"`, ignoring backslash escapes. A source string
  containing `\"` was mis-parsed: OLD petta throws `Syntax error: missing ')'`
  on `!("a\"b")`. The patch threads an escape-state variable.
- `src/parser.pl` (escape_quotes): printing did not escape backslashes, so
  `\` did not round-trip.

VERIFIED: old petta syntax-errors on `!("a\"b")`; patched petta parses it.
Blast radius on the corpus: 4 files use backslash-in-string (parse, repr,
test_string_comments, prologimport). All coverage measurements that depend on
this patch are labeled; the patch is applied to the local PeTTa checkout only,
never committed upstream without Hammer's review.
