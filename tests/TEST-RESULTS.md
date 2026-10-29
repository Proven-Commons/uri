# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: a strict Python reading of RFC 3986 written in the harness (Python 3.12.3): the stepwise split of Appendix B, merge by section 5.2.3, dot segment removal by the buffer algorithm of section 5.2.4, the strict transform of section 5.2.2, recomposition by section 5.3
- Second voice: urllib.parse.urljoin from the same Python; disagreements with the tool where the oracle sides with the tool are counted apart as named differences, never as failures
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261026
- Section 5.4.1 normal cases: 23 of 23 agreements
- Section 5.4.2 abnormal cases (strict): 19 of 19 agreements
- Section 5.2.4 dot cases (with the oracle checked against the same hand written expectations): 36 of 36 agreements, 0 oracle disagreements with the hand list
- Split fixed cases (shown form, see the harness note): 10 of 10 agreements
- Absent versus empty resolution cases: 3 of 3 agreements
- Malformed requests answered error: 15 of 15
- Generated pairs: 3200 (resolve 3200 of 3200 agreements; split of every distinct generated string 5484 of 5484 agreements)
- urljoin agreements on generated pairs the oracle settled for the tool: 1203; counted apart as named differences: 1997
- Differential inputs: 8790
- Differential agreements: 8790
- Named differences:
  - `http:g` against `http://a/b/c/d;p?q` (fixed case): the strict reading keeps the reference as it stands, giving `http:g`; urljoin drops a scheme that matches the base and gives `http://a/b/c/g`.
  - urljoin returns the reference unchanged; the base takes no part: 1746 cases
    - base `A1:`, reference `//?name=ferret#nose`: tool and oracle give `A1://?name=ferret#nose`; urljoin gives `//?name=ferret#nose`
    - base `A1:`, reference `//a.b.c/g../..././mid`: tool and oracle give `A1://a.b.c/g../.../mid`; urljoin gives `//a.b.c/g../..././mid`
    - base `A1:`, reference `//a/`: tool and oracle give `A1://a/`; urljoin gives `//a/`
  - other urljoin readings: 225 cases
    - base `http:`, reference `/..g/?q#s`: tool and oracle give `http:/..g/?q#s`; urljoin gives `http:///..g/?q#s`
    - base `http:`, reference `/_/-/../b`: tool and oracle give `http:/_/b`; urljoin gives `http:///_/b`
    - base `http:`, reference `?y/../x#`: tool and oracle give `http:?y/../x#`; urljoin gives `http://?y/../x`
  - urljoin reads a reference whose scheme matches the base in the non-strict way: 26 cases
    - base `http:`, reference `http:./seg/a/-?q`: tool and oracle give `http:seg/a/-?q`; urljoin gives `http:///seg/a/-?q`
    - base `http:/`, reference `http://?name=ferret#s`: tool and oracle give `http://?name=ferret#s`; urljoin gives `http:///?name=ferret#s`
    - base `http:/./`, reference `http:/mid/a:b/g../#s/./x`: tool and oracle give `http:/mid/a:b/g../#s/./x`; urljoin gives `http:///mid/a:b/g../#s/./x`
- Failures: 0
