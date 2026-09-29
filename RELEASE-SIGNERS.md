# Assurance release signers

This file names the key that signs the most recent Tacenta assurance tags and
shows how to check a signature with it. It also says what that check does and
does not establish.

## Read this first

This file lives in the repository it describes, so a copy of it proves nothing
by itself. Someone who can push to the repository, or who runs a mirror, can
publish a different key here. Before you trust a fingerprint below, compare it
with a source outside this repository tree.

Public sources outside the tree are GitHub's key listing for the maintainer
account, <https://github.com/will-natuvea.keys>, which lists the same key as an
*authentication* key, and, once the key is registered as a signing key,
<https://api.github.com/users/will-natuvea/ssh_signing_keys>. Until the key is
registered as a signing key, GitHub shows these tags as "Unverified". That badge
does not mean the signature is bad.

Tags named `tacenta-assurance-*` and `tacenta-spec-*` are covered by a
repository ruleset that blocks deleting or updating them. Anyone can read it at
<https://api.github.com/repos/Natuvea/tacenta-core/rulesets>. The name check
below still applies, because a ruleset is a setting and this file is a copy.

## Maintainer key

| Identity | Email | Algorithm | SHA-256 fingerprint |
| --- | --- | --- | --- |
| `will-natuvea` | `info@natuvea.com` | SSH Ed25519 | `SHA256:7hdUimAm+JNOFo8YR3RRoHKHHXFxhqBRUHwEzt2xAV4` |

Public key:

```text
ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIEr4DQjmMEn5Wf9l6tBF+sl7vzJcayYR4CPPw6y/N/r8 will-natuvea
```

This maps a GitHub handle and a mailbox to a key. It does not identify a
natural person.

## Authority and change

- **One signer today.** A tag signed by any other key fails verification
  against this file. Other accounts have tagged in this repository.
- **One key, two jobs.** The same key authenticates the maintainer account to
  GitHub, so a compromise of one is a compromise of the other.
- **What a signature shows.** It shows possession of the key when the tag was
  made. It does not show that a review took place, and a tag's date is
  self-asserted.
- **Custody.** This file does not say where the private key is kept.
- **Change.** A change of key will be recorded in this file and announced
  through the security contact in `SECURITY.md`. Tags signed before a change
  stay valid for the key that signed them.

## Assurance tags

Signed with the key above:

| Tag | Tag object | Tagged commit |
| --- | --- | --- |
| `tacenta-assurance-v0.4.1` | `18755545985cee1039df7ab0e209f4c34d2abf35` | `abd0c3b18a76cb34931536ddc368256227e06c37` |
| `tacenta-assurance-v0.4.2` | `2ff70100f8804cba1dc38a63811b07e033acd1c1` | `d072ef2e85628ed8a9916d42aae1222c8f24c9a0` |
| `tacenta-assurance-v0.4.3` | `59d2594db082144b45dbd984489341b04d05b8c8` | `2c89e0898b88231c54ffa5e9058817ea3f0cda75` |

**Not signed.** `tacenta-assurance-v0.2.0`, `tacenta-assurance-v0.3.0`,
`tacenta-assurance-v0.4.0`, `tacenta-spec-v0.1.0` and `tacenta-spec-v0.2.0` are
annotated but carry no signature, and `git tag -v` reports `no signature
found` for them. An unsigned tag has no authenticity beyond access to the
repository. `tacenta-assurance-v0.3.0` was tagged by a different account.

The key signs the tag objects, not the tagged commits. Those commits are
either unsigned or carry GitHub's own signature from a squash merge.

## Verification

You need Git 2.34 or later and OpenSSH's `ssh-keygen`. Run this inside a clone,
after fetching tags (a shallow clone does not have them):

```sh
git fetch --tags origin

cat > allowed-signers <<'EOF'
will-natuvea,info@natuvea.com namespaces="git" ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIEr4DQjmMEn5Wf9l6tBF+sl7vzJcayYR4CPPw6y/N/r8
EOF

git -c gpg.format=ssh -c gpg.ssh.allowedSignersFile="$PWD/allowed-signers" \
  tag -v tacenta-assurance-v0.4.3
```

The check passes only if the output includes this line and the exit status is
zero:

```text
Good "git" signature for will-natuvea with ED25519 key SHA256:7hdUimAm+JNOFo8YR3RRoHKHHXFxhqBRUHwEzt2xAV4
```

`Good "git" signature with ED25519 key ...` without the words `for will-natuvea`
means a valid signature by a key that is not in your file. Treat that, and
anything else, as a failure.

A valid signature does not tie the tag to its name. Check that the tag records
the name you asked for and the commit in the table above:

```sh
git for-each-ref refs/tags/tacenta-assurance-v0.4.3 --format='%(tag) %(*objectname)'
```

It must print exactly:

```text
tacenta-assurance-v0.4.3 2c89e0898b88231c54ffa5e9058817ea3f0cda75
```

Then read `CLAIMS.md`, `LIMITATIONS.md` and `ASSURANCE.md` at that tag, for
example with `git show tacenta-assurance-v0.4.3:tacenta-proofs/CLAIMS.md`, for
the scope and limits of the release. A signature says who tagged the commit; it
says nothing about what the commit proves.
