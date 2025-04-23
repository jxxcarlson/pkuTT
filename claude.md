
# Bash commmands
- agda: run agda on a file. If `agda Foo.agda` produces output,
the output describes the typecheck errors. If there is no output,
that means tha the file compiles, i.e., there are no typecheck errors.

# Workflow

- When a code change is accepted, always run `agda` on the fila and take the output, if any, as input for the next round of analysis by Claude.  Do this automatically.
