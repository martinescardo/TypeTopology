## Notice

A few Agda files in this directory are links to Agda files in subdirectories. This is done to avoid breaking links in published papers after the files were moved to suitable directories. Please do not move or remove them.

To add other indirection, create a file, and import it in either `Published/index.lagda` (if the file is published by a contributor) or `Cited/index.lagda` (if the file is cited by other authors).

To check that everything is fine, typecheck AllModulesIndex, which includes the index files in `Published` and `Cited`.
