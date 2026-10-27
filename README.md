# uri

A Lean implementation of URI reference resolution. This is a Proven Commons project: it rebuilds a widely used rule in Lean and proves the new code follows its written specification.

Status: not verified. No code has landed yet, and no plan issue has been posted. The specification has not been approved by a reviewer, so do not call this verified.

## First slice

URI reference resolution, as in RFC 3986, sections 3 and 5.2.

- Split a reference into five parts.
- Merge paths.
- Remove dot segments.

Section 5.2 leaves percent escapes as written, so this slice needs no escape handling. Normalization, as in section 6.2.2, comes later and would import percent encoding from the codec project. A full grammar check is the second slice.

## Main claim

Removing dot segments leaves no "." or ".." and is idempotent. Resolving against an absolute base gives an absolute URI. All worked examples of section 5.4 hold.

## Test oracles

- RFC 3986 section 5.4.
- uriparser.
- Go URL.ResolveReference.
- Python urljoin, with a mode for its reading of "http:g".

## Score

14 out of 18, from two scorers, in the round 3 sheet in the mission repo. The sheet is mission pull request 17.

## What is not in this slice

- Percent escape handling, except as written.
- Normalization.
- The full URI grammar.
- Any claim about a full URL implementation. Browsers follow the WHATWG URL Standard, which departs from RFC 3986 on purpose.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
