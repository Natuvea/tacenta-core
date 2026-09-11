# Identities and devices

Identity keys, devices, and how they relate.

Status: partial. The identity key's secret and application signatures are
specified below. Devices, and how they relate to identities, are a scaffold
and unspecified.

## The identity key's secret

An identity is one 32-byte secret, generated as 32 random bytes. Exporting an
identity yields those 32 bytes as they are, and importing takes the same 32
bytes back as they are. An imported identity carries no prekeys and no
sessions; those are persisted separately (session-persistence.md).

The same 32 bytes serve both roles the identity key has (ADR-0002):

- the X25519 private scalar, clamped when used, in every Diffie-Hellman
  computation under the identity key (session-establishment.md);
- the XEdDSA private key, for every signature made under the identity key.

## Application signatures

An identity also signs messages an application supplies, such as a server's
challenge to a device. The signature is XEdDSA under the identity key over the
message with a fixed label in front:

```
input     = "tacenta:application-signature:v1" || 0xFF || message
signature = Sig(IK, input, Z)
```

The label is 32 ASCII bytes, and with its `0xFF` terminator 33 (CONSTANTS.md).
A verifier rebuilds `input` from the message and verifies the signature under
the published identity key.

Prekey signatures carry no label (session-establishment.md, Publishing keys).
The label is what keeps the two uses of the one key apart: a signature made
for one is not accepted for the other.
