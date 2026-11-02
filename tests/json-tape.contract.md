# JSON tape decoding

A tape is its input plus the tokens read from it, and a token carries a span,
not a decoded payload.  `decodeTape` reads the tape against its own input and
returns `some v` only when every token's span points at the bytes its kind
denotes, the tokens are consumed exactly, and the input is consumed apart from
whitespace at both ends.  `spansWellFormed` decides the span discipline alone:
every span lies inside the input, is non-empty, and starts at or after the
previous span's stop.

The scenario builds its tapes by hand — none is produced by the parser — so a
span that is wrong about its bytes is observable even when its kind is
plausible.  No compiler, proof checker, network, clock or service is reached.

    nix develop -c lake env lean tests/json-tape.lean

### JC3 — the decoder reads the bytes and the span predicate reads the spans

- **Actor:** an operator running the tape scenario.
- **Given:** hand-built tapes over their own input:
  - `[1]` with an opening-bracket span, a number span over `1`, and a
    closing-bracket span, in order;
  - `[1,2]` with an opening-bracket span, a number span over `1`, a comma span
    over `,`, a number span over `2`, and a closing-bracket span, in order;
  - `"a"` with one string span over the whole literal;
  - `a"` with one string span over the whole two bytes, every span in bounds
    and the byte at its start `a`, not the opening quote;
  - `{"a":1}` with an opening-brace span, a string span over the name, a colon
    span over the byte between the name and the value, a number span over `1`,
    and a closing-brace span, in order;
  - `{"a":1}` with the colon token absent;
  - `{"a":1}` with the colon token spanning `⟨5, 6⟩` while the cursor the name
    leaves is at the byte `4`, a one-byte-short span;
  - tokens for `[1,2]` laid over `[1x2]`, every span in bounds, the comma token
    between the two number tokens, and the byte at the comma's cursor `x`;
  - a number token spanning `abc`;
  - a string token spanning `"ab` but not the closing quote;
  - a string token spanning `"\uDEAD"`, the unpaired escape RFC 8259 §8.2 admits;
  - an opening-bracket token over the byte `{`;
  - tokens for `[]` over `[1]`;
  - tokens for `[]` over `[ ]`;
  - a number token for `1` over `1 2`;
  - a number token for `1` over ` 1 `;
  - two number tokens whose spans overlap;
  - no tokens over `1`.
- **When:** the operator elaborates the scenario with the command above.
- **Then:** the `lean` process exits 0, and every assertion holds:
  - the correct tape decodes to `some (.array [.number [0x31]])` and
    `spansWellFormed` is `true`;
  - the correct two-element tape decodes to
    `some (.array [.number [0x31], .number [0x32]])` and its spans are well
    formed, so the comma path has an accepted instance;
  - the correct string tape decodes to `some (.string [0x61])` and its spans
    are well formed;
  - the `a"` tape decodes to `none` although its span is well formed: the byte
    at the span's start is `a`, not `"`, so only the opening-quote check can
    refuse it;
  - the correct object tape decodes to
    `some (.object [([0x61], .number [0x31])])`, its spans are well formed, and
    its colon token's span is `⟨4, 5⟩`, naming the `:` byte at offset `4`;
  - the object tape with no colon token decodes to `none`, so a separator the
    tape does not carry cannot be supplied by the decoder;
  - the object tape whose colon span is `⟨5, 6⟩` decodes to `none`, so the
    colon is checked at its byte and not only by its presence;
  - the comma tape laid over `[1x2]` decodes to `none` although its spans are
    well formed: a comma is matched as a token and at its byte, and the byte at
    its cursor is `x`;
  - the number token over `abc` and the short string token both decode to
    `none`, and the short string token's spans are still well formed, so the
    refusal is the decoder's reading of the bytes rather than the span
    predicate's;
  - the `"\uDEAD"` tape decodes to `none` although its span is well formed:
    the decoder's character discipline is the strict reading, so a tape over a
    text `Policy` refuses does not decode;
  - the opening-bracket token over `{` decodes to `none`;
  - `[]` over `[1]` decodes to `none`, while the same token kinds over `[ ]`
    decode to `some (.array [])`;
  - `1` over `1 2` decodes to `none`, while `1` over ` 1 ` decodes to
    `some (.number [0x31])`;
  - the overlapping spans are `spansWellFormed = false`, while the correct
    tape's spans are `spansWellFormed = true`;
  - the empty token list decodes to `none` and its spans are well formed.
- **Why:** a tape is not valid because a parser produced it, and a token kind
  is not evidence about the bytes it names.  The affirmative controls decode
  the same token kinds that the refused cases use where the difference is only
  the input or the gap, so a refusal is attributable to the span-to-bytes
  relation rather than to a detector that rejects every tape.  The short string
  span and the overlapping spans are separated deliberately: the first is
  well-formed by the span predicate and refused by the decoder, and the second
  is refused by the span predicate although its token kinds are ordinary.  The
  `"\uDEAD"` tape carries the same separation at the character level: its span
  is well formed and its bytes are an RFC text, and the decoder refuses the
  reading because its discipline is `Policy`'s strict reading.  The correct
  string and object tapes are what make those refusals evidence: without them,
  a decoder that refused every string, or every non-empty object, would pass
  every assertion the scenario makes about a refusal.  The colon and comma
  cases separate a separator's presence from its position: the tape must carry
  the token, and the token's span must name the byte at the cursor, so a
  decoder that matched only the token kind would accept `{"a" 1}` or `[1 2]`
  as if the separator were there.
