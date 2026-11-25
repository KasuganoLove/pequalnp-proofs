# Exact Gröbner tooling audit for the held L-gct-232 task

Read-only audit completed 2026-11-25, with live Magma metadata retrieved at **08:42:05 UTC**. No solver request, remote POST, browser action, binary download, installation, or polynomial upload was performed.

## Recommended available route

The new official Magma calculator publishes a REST API. The University of Sydney's existing Magma site links the new site, and the calculator's own HTML sets `window.MAGMA_CALC_API_URL` to `https://calculator.magma-maths.org/execute`.

- University provenance: <https://magma.maths.usyd.edu.au/magma/contact/>
- Calculator: <https://magma-maths.org/calc/>
- Client source: <https://magma-maths.org/static/js/calculator.js>
- Official API documentation: <https://github.com/Magma-Maths/calculator>
- Live read-only configuration: <https://calculator.magma-maths.org/info>
- Live version: <https://calculator.magma-maths.org/version>

The documented computation request is **POST `/execute`** with JSON `{"code":"Magma source"}`. Authentication is not shown in the public API contract. No request was sent to that endpoint in this audit.

The fresh `/info` response had `Cache-Control: no-store` and reported:

| Field | Value |
|---|---:|
| Wall time | 300 seconds |
| CPU time | 300 seconds |
| Guest memory, including OS and agent | 1,073,741,824 bytes |
| Input | 51,200 bytes |
| Output | 20,480 bytes |
| Concurrent computations per IP | 2 |
| Requests per minute / hour | 60 / 300 |
| Waiting queue | 0 |

Version metadata reports Magma **2.30-1**, calculator revision `7ce9bd0e89a0edd6cedd3cd0e5312043be1bc6f0`. Code and IP are logged, with a minimum submission-retention period of 90 days. Only the already-public mathematical data is appropriate for any later authorized computation.

The API returns success, stdout, exit status, truncation, resource metadata, and warnings. Timeouts, runtime errors, or truncated output return `success: false`. HTTP 413 means input too large, 422 malformed/missing code, 429 rate/concurrency restriction, and 503 unavailable executor. `/info` and `/version` do not run computations; `/health/deep` does run a test job and was deliberately not requested.

The legacy <https://magma.maths.usyd.edu.au/calc/> documents only 60 seconds and 50,000 input bytes. Direct urllib access returned HTTP 401 in this workspace. The new official API's read-only endpoints succeeded. Solver execution itself remains untested.

## Exact identity extraction

For characteristic-zero impossibility, the useful deliverable is coefficients `c[i]` with `sum c[i]*F[i] = 1`, where `F` is the exact original list of chart equations. Such an identity can be rechecked independently and translated into Lean polynomial arithmetic; a remote verdict alone is not a Lean proof.

Magma documents `IdealWithFixedBasis(F)` and `Coordinates(I, f)`. With a fixed basis, coordinates refer to the original list `F`; with an ordinary ideal they refer to the Gröbner basis instead. A proposed, **unexecuted** computation core is:

```magma
// R is the rational polynomial ring; F is the exact equation sequence.
I := IdealWithFixedBasis(F);
Groebner(I : Al := "Direct", GlobalModular := false);
if R!1 in I then
    c := Coordinates(I, R!1);
    assert &+[c[i]*F[i] : i in [1..#F]] eq R!1;
    print c;
end if;
```

The handbook warns that fixed-basis tracking can be much more expensive. A discovery computation without tracking may be useful before the certificate run. The rational-field default uses a Monte Carlo global-modular reconstruction; the documented `GlobalModular := false` switches to the step-by-step algorithm. Any exported certificate should still be independently checked. The 20 KiB output cap may prevent returning a large certificate; no output-cap bypass is proposed.

Primary documentation:

- Ideals and fixed bases: <https://magma.maths.usyd.edu.au/magma/handbook/text/1313>
- Gröbner algorithms, coordinates, and global-modular parameter: <https://magma.maths.usyd.edu.au/magma/handbook/text/1314>
- Monomial orders: <https://magma.maths.usyd.edu.au/magma/handbook/text/1312>

## Local Singular fallback

The official download index currently lists `Singular-4.4.1-Rocky8.tar.gz` (14 MB, 2025-04-23) and `Singular-4.4.0-x86_64-Linux.tar.gz` (22 MB, 2024-09-11):

<https://www.singular.uni-kl.de/ftp/pub/Math/Singular/UNIX/>

Official installation instructions explicitly permit unpacking into a user-owned directory without root. Preserve the tarball's directory layout so the executable can find its sibling libraries. Do not copy the executable alone. No binary was downloaded, so bundled dependencies and compatibility with this workspace remain unverified. Readline is documented for optional interactive completion/history; the installer notes do not provide a complete current ELF dependency list. The published MD5 for the 4.4.1 archive is `bd2a46b1fc4ad8b48c55531083d34f18`; this is the publisher's legacy integrity check, not a modern cryptographic authenticity guarantee.

Singular has a documented direct certificate operation: `sm = liftstd(I,T)` returns a standard basis and a matrix satisfying `matrix(sm) = matrix(I)*T`. If the standard basis is the unit ideal, the corresponding column gives a polynomial combination of the original equations equal to 1. Both `"std"` and `"slimgb"` are documented algorithm choices.

- Installation: <https://www.singular.uni-kl.de/ftp/pub/Math/Singular/UNIX/INSTALL_unix.txt>
- Transformation certificate: <https://www.singular.uni-kl.de/Manual/latest/sing_294.htm>

## Saved evidence and scope

The adjacent JSON responses and retrieval manifests preserve exact URLs, response dates, live limits, and version. The third-party HTML, JavaScript, API README, installation text and checksum list were inspected at the linked primary sources; their full contents are not redistributed in this checkpoint. This audit establishes an advertised, reachable read-only service and a documented computation protocol. It makes no claim that the full 18-variable systems finish within service limits, that any certificate exists, or that a chart result establishes the global theorem without the chart coverage argument.
