# JSON API

`parseDocument (limits) (input)` returns one of four outcomes: a tape over the
input, an `invalid` rejection carrying a reason, or one of the resource
outcomes `inputTooLong`, `depthExceeded` and `outOfCapacity`.  A rejection is a
claim about the input; a resource outcome is a claim about the limits and says
nothing about whether the input is valid.  `decodeTape` reads a tape back to a
`Value`, and a tape whose spans do not point at the bytes their token kinds
denote yields `none`.

The base language is RFC 8259's grammar, with RFC 3629's encoding in its
`UTF8-char` production, and `Policy` is the character restriction on top of it
(RFC 7493 §2.1).  A refusal whose reason is `Policy` — `unpairedSurrogate` or
`noncharacter` — refuses a text the grammar admits, so the scenario names that
reason rather than treating every `invalid` as a non-text.  Duplicate member
names are RFC-legal and preserved; I-JSON's uniqueness rule is not adopted.

This scenario is a Lean program of `#guard` checks and two `example` proofs,
elaborated against the public entrypoint, so it observes the same interface a
client does.  Accepted documents are compared through `decodeTape`, not by
inspecting a parser-private structure, and no accepted case is judged on the
decoded value alone: `accepts` requires both the decoded value and
`t.input = input.toList`.  The program builds its own inputs; no
compiler, proof checker, network, clock or service is reached.

    nix develop -c lake env lean tests/json-api.lean

### JC1 — the API accepts, refuses, and distinguishes a bound from a fault

- **Actor:** an operator running the API scenario.
- **Given:** `Limits.default`, and inputs that are ASCII documents except where
  a byte sequence or an escape is the case under test.
  - Accepted inputs: `null`, `true`, `{"a":1,"a":2}`, `{"a":1,"b":2,"a":3}`, a
    number whose lexeme is longer than a machine word, `[ 1 , 2 ]`, ` 1 `; the
    raw UTF-8 sequences `C3 A9`, `E2 82 AC`, `F0 90 8D 88`, `F0 90 80 80` and
    `F4 8F BF BD` (U+10FFFD, the last permitted scalar) inside a string; raw
    `7F` inside a string; an object whose braces, name, colon, value and
    closing brace are separated by tab, CR, LF and space; `-0`, `1E+3`,
    `-1.5E-7` and `1.25e10`; the escaped pair
    `"\uD834\uDD1E"`, the raw encoding `F0 9D 84 9E` of the same code point,
    `"\uD800\uDEAD"` and `"\uFFFD"`.
  - Refused inputs: `01`, `-`, `+1`, `.5`, `1.`, `1e`, `1 2`, `NaN`, `0x10`,
    `--1`; malformed UTF-8 inside a string — lone `80`, truncated `C3`,
    truncated `E2 82`, overlong `C0 AF` and `E0 80 AF`, encoded surrogates
    `ED A0 80` and `ED BF BF`, `F4 90 80 80`, five-byte `F8 88 80 80 80`, and
    `FF`; raw controls `00`, `1F`, `09` and `0A` inside a string; a form feed
    or vertical tab where `ws` is required; and `EF BB BF 31`.
  - `Policy` refusals whose reason is named: `"\uDEAD"` and `"\uD800"`
    (`unpairedSurrogate`); `"\uFDD0"`, `"\uFFFE"`, `"\uFFFF"`, raw `EF B7 90`,
    raw `EF BF BE`, raw `F4 8F BF BF` (U+10FFFF), raw `F0 9F BF BE`
    (U+1FFFE), and `"\uDBFF\uDFFF"` — the well-formed pair that encodes
    U+10FFFF — (`noncharacter`).
  - Limit cases, on the same entry with a narrowed bound: `[1]` under
    `maxInput := 2`, `[[1]]` under `maxDepth := 1`, `[1,2]` under
    `maxTokens := 4`, and `01` under `maxInput := 2`, `maxDepth := 0` and
    `maxTokens := 0`.
- **When:** the operator elaborates the scenario with the command above.
- **Then:** the `lean` process exits 0, and every assertion holds:
  - every accepted case checks that the tape's `input` is exactly the bytes
    supplied; `null` decodes to `some .null` and `true` to
    `some (.bool true)`.
  - `{"a":1,"a":2}` decodes to two members in source order, both keyed `[0x61]`
    and carrying the lexemes `1` and `2`; `{"a":1,"b":2,"a":3}` decodes to
    three members in that order, the repeated name in the last position.  No
    member is dropped and no key wins.
  - The long number decodes to a number whose lexeme is exactly those bytes;
    the number-grammar cases decode to their own lexemes.
  - Each accepted UTF-8 sequence decodes to its code point; raw `7F` decodes to
    `some (.string [0x7F])`; the whitespace-separated object decodes to its one
    member; the escaped pair, its raw encoding and `"\uD800\uDEAD"` decode to
    `[0x1D11E]`, `[0x1D11E]` and `[0x102AD]`; `"\uFFFD"` decodes to
    `some (.string [0xFFFD])`.
  - `01`, `-`, `+1`, `.5`, `1.`, `1e`, `1 2`, `NaN`, `0x10`, `--1`, every
    malformed UTF-8 sequence, every raw control, every non-`ws` whitespace
    case, and `EF BB BF 31` return `.error (.invalid _)`; the byte-order mark
    returns `.error (.invalid .byteOrderMark)`.
  - `"\uDEAD"` and `"\uD800"` return `.error (.invalid (.unpairedSurrogate _))`;
    the three noncharacter escapes, the two raw BMP noncharacters, U+10FFFF
    raw and as the pair `"\uDBFF\uDFFF"`, and raw U+1FFFE return
    `.error (.invalid (.noncharacter _))`.
  - An `example` proves `∃ v, RfcText (bytes of "\uDEAD") v ∧ ¬ Policy v`: the
    same bytes have an RFC 8259 reading, and `Policy` is what refuses it.
  - An `example` shows that a successful `parseBytes` of `[1]` yields a
    `ValidDocument`, the conjunction `RfcText ∧ Policy`.
  - `[1]` under the default limits parses; the same input under `maxInput := 2`
    returns `.error .inputTooLong`; `[[1]]` under `maxDepth := 1` returns
    `.error .depthExceeded`; `[1,2]` under `maxTokens := 4` returns
    `.error .outOfCapacity`.
  - `01` returns `.error (.invalid _)` under a length bound equal to its own
    length and under a depth or capacity bound that could not have excluded
    its syntax, so the fault is not relabelled by a resource outcome.
- **Why:** the clause map in docs/contract.md makes the byte-level details normative: strict UTF-8
  is RFC 3629's nine alternatives inside RFC 8259's grammar, raw controls are
  excluded by §7's `unescaped` ranges, `ws` is §2's four bytes, and the number
  grammar is §6's with the leading-zero rule.  The restrictions we choose on
  top of the standard are the byte-order mark, unpaired escapes and
  noncharacters, and the scenario shows that the last two are refusals of RFC
  texts by naming their reason and by proving the RFC reading exists.  U+10FFFF
  is itself a noncharacter (RFC 7493 §2.1's `n % 0x10000 = 0xFFFF`), so the
  accepted encoding boundary is U+10FFFD; refusing the raw encoding and the
  surrogate pair that spells the same code point exercises the predicate's
  `U+nFFFF` and pair branches rather than only the BMP cases.  An API
  that reports a resource outcome for valid input is usable only if it never
  reports one for a syntax fault; comparing accepted values through
  `decodeTape` makes those cases statements about the input rather than about
  the parser's internal state, and the paired tight-limit cases separate a
  bound from a refusal at the same entry point.  Duplicate names are asserted
  as preserved, not unique, because uniqueness is the RFC's `SHOULD` and
  I-JSON's rule is not this API's policy.
