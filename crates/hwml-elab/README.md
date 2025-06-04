# HMWL Elaborator

This crate consists of the elaboration (and de-elaboration) code for HWML. Elaboration is the process of translating surface level syntax (what humans read and write) into the core language of HWML.

The core language is massively simpler than the surface language, making it much easier for a machine to check and manipulate. The surface language has many affordances for human beings which complicate the language.

## Elaboration Activities

- type check and synthesis
- solve implicit arguments
- solve instance arguments
- erase symbolic names
- solve meta-variables (when possible)

## De-elaboration Activities
