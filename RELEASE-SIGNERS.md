# Assurance release signers

This file maps the signer used for Tacenta assurance tags to a public key so
an outside reader can verify the tag object without trusting the repository's
web UI.

## Maintainer key

| Identity | Email | Algorithm | SHA-256 fingerprint |
| --- | --- | --- | --- |
| `will-natuvea` | `info@natuvea.com` | SSH Ed25519 | `SHA256:7hdUimAm+JNOFo8YR3RRoHKHHXFxhqBRUHwEzt2xAV4` |

Public key:

```text
ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIEr4DQjmMEn5Wf9l6tBF+sl7vzJcayYR4CPPw6y/N/r8 will-natuvea
```

The private key is not stored in this repository.

## Assurance tags

The following annotated tags were signed by the key above:

| Tag | Signed object |
| --- | --- |
| `tacenta-assurance-v0.4.1` | `abd0c3b18a76cb34931536ddc368256227e06c37` |
| `tacenta-assurance-v0.4.2` | `d072ef2e85628ed8a9916d42aae1222c8f24c9a0` |
| `tacenta-assurance-v0.4.3` | `2c89e0898b88231c54ffa5e9058817ea3f0cda75` |

The tag objects are annotated and carry SSH signatures. This mapping records
who the key belongs to; it does not make the signed commits an audit or widen
the claims in `tacenta-proofs/CLAIMS.md`.

## Verification

After cloning the repository and fetching tags, save the public key in an
allowed-signers file with this line:

```text
will-natuvea,info@natuvea.com ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIEr4DQjmMEn5Wf9l6tBF+sl7vzJcayYR4CPPw6y/N/r8
```

Then configure Git for SSH signature verification and verify a tag:

```sh
git config gpg.format ssh
git config gpg.ssh.allowedSignersFile /path/to/allowed-signers
git tag -v tacenta-assurance-v0.4.3
```

The tag's signed object should match the commit listed above. Always inspect
`CLAIMS.md` and `ASSURANCE.md` at that exact commit for the scope and limits of
the assurance release.
