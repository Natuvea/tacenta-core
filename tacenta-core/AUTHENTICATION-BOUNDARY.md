# The authentication boundary

Every function here consumes a message **before anything has authenticated it**.
That is the most sensitive place in this codebase, so each one is registered
with the argument for why it is safe, and
`tooling/check_authentication_boundary.py` fails the build if the code and this
list disagree in either direction.

Identity is the file path and the function name, joined by a double colon, as
in the tables below. Bare names are not enough: a second function called
`receive` anywhere in the tree would otherwise count as registered because the
first one was.

## What this enforces, and where that is stated

The property is "nothing durable moves until the authenticator verifies". What
that property is *for* is stated in the consuming product's
identity-change and replay policy: which replays are refused, which are
expected, what happens when an identity changes, and where the guarantees
stop. This registry is the enforcement; that record is the claim being
enforced. The two are kept separate so that the enforcement always has a
statement to be checked against; a guarantee that stops after thirty-two peers,
for example, is stated there rather than left implicit here.

## What the gate checks, and what it does not

`tooling/check_authentication_boundary.py` checks three things: that every
function in the zones whose name contains a consuming verb is a row in one of
the tables below; that every row still names a function; and that the
function's signature has the shape its table promises -- `&self` under
"Transactional" (`&mut self` for the adopting `commit`), `&mut self` under
"Mutating". It does not read a body. That a receive clones before it assigns,
or verifies before it deletes, is an argument, and the arguments are in the
rows and in `tests/failed_decrypt_changes_nothing.rs`, which is the test that
holds the property.

The gate is deliberately strict about what counts as registered: only a table
row whose first cell is `` `path::name` `` registers a function, never a
backticked name in prose; `#[cfg(test)]` exempts a function only as the
attribute directly on the item, never as nearby text; and verbs are matched
anywhere in a name, so a function such as the braid's `step_receive` is
discovered along with the `receive` that wraps it.

## Why a registry rather than a rule

The rule would be "do not commit state before the authenticator verifies". A
rule stated in a specification, a `LIMITATIONS` entry, or a source comment is
not checked by anything, and a rule nothing checks is not a rule. A registry
that the build compares against the code is.

## Why the check runs in both directions

The check verifies that everything the code has is written down, **and that
everything written down still exists**. The second direction is what catches a
registry that has drifted from the code: a row for a function that no longer
exists, or that has moved, would otherwise make the gate read as though it
covered something it no longer looked at.

Discovery covers private functions as well as `pub fn`, because the function
that matters most here, `Session::decrypt_ratchet`, is private; and it matches
verbs anywhere in the name, because `establish_responder` starts with none of
the obvious ones.

## The distinction that matters

**Deriving is not committing.** A receive path must derive a key to check an
authenticator at all, so "touch no state" is impossible. What is possible is
that nothing durable moves until the caller says so, which is why the safe shape
is a candidate and a `commit` rather than a mutation and a hope.

## Registered

### Transactional: they cannot commit

Take `&self`, return the state a message would produce. The caller adopts it
only after the message authenticates, so the unsafe use is unavailable rather
than discouraged.

| function | returns |
|---|---|
| `tacenta-core/triple/src/lib.rs::receive` | `(State, Key)`, adopted by `commit` |
| `tacenta-core/triple/src/lib.rs::commit` | the adopting half |
| `tacenta-core/braid/src/lib.rs::receive` | `(u64, Option<Output>, Braid)`, adopted by `commit` |
| `tacenta-core/braid/src/lib.rs::step_receive` | the receive logic proper: `&self`, takes the current `State` by value and returns the next one; `receive` wraps it and hands back the candidate `Braid`. Registered separately because the gate matches verbs anywhere in a name. |
| `tacenta-core/braid/src/lib.rs::commit` | the adopting half |

### Orchestration, transactional by construction

| function | how |
|---|---|
| `tacenta-core/src/sessions/lifecycle.rs::decrypt_ratchet` | clones the ratchet, verifies the tag, then assigns. Private, and the function this registry exists for: it is the one that touches the most state on the receive path. |
| `tacenta-core/src/sessions/lifecycle.rs::decrypt` | the public wrapper; does no state change of its own beyond clearing `pending_initial` after a successful decrypt |
| `tacenta-core/src/sessions/lifecycle.rs::establish_responder` | reads prekeys, authenticates, then deletes. The one consuming function here whose name does not start with a consuming verb. |
| `tacenta-core/src/sessions/lifecycle.rs::establish_initiator` | consumes a peer's published bundle, which an attacker supplies through the directory. Verifies both prekey signatures before deriving, and holds no local state that a failure could consume: a refusal leaves this party exactly as it was. |

### Mutating, and safe only because of a caller

Take `&mut` and will advance live state if called on it. Correct today because
**every caller clones first**, which is a property of the callers and not of
these functions. A new caller reaching past the composition layer would commit
state before the authenticator verifies, with no signature change to warn
anyone.

| function | who guarantees the transaction |
|---|---|
| `tacenta-core/ratchet/src/lib.rs::receive` | `triple::receive` clones `State` first; `decrypt_ratchet` clones its own |
| `tacenta-core/spqr/src/lib.rs::receive` | `triple::receive` clones the whole composite first |

**Neither is defended by its own type.** Making them `&self`-and-commit would
close that at the cost of a second candidate allocation per message on a path
that already clones once. Not judged worth it; if a third caller appears, it
should be.

## The send direction

`Triple::send` runs both ratchets against a copy of the composite and assigns
on success, so a post-quantum failure cannot consume a classical message key
for a message never sent.

It keeps `&mut self` rather than becoming a candidate and a `commit`, because
there is no authenticator to wait for: a caller has nothing to decide between
deriving and committing, so the ceremony would buy nothing.

The test that covers it asserts that the message numbers are consecutive
across a failure.

`tacenta-spqr::State::send` can still advance an agreement output before
returning an error. Through `Triple::send` that is covered, because the whole
composite is the copy. A direct caller is not, which is the same shape as the
two mutating receive paths above and is watched the same way.
