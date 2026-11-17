# Documentation

- Keep `README.md` limited to essential instructions for building and running the
  project.

# Comments

- Only add short and concise comments when they are essential to understanding the code.

# Formatting

- In long signatures, put each argument on a separate line.
- Always put each sum type constructor on a separate line.
- Prefer to use named arguments when there are more than one wildcards in a pattern.
- Prefer to use named fields over tuple syntax when there are multiple fields.
- Define instances with named fields.

# Pattern matching

- Avoid catch-all `_` arms when matching on a sum type; list every constructor
  so that adding one forces a decision. The same applies to refutable patterns.

# Default values

- Prefer to avoid default values. Default proofs are fine and encouraged when
  they make sense.
