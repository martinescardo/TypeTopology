## Notice

A few Agda files in this directory are links to Agda files in subdirectories. This is done to avoid breaking links in published papers after the files were moved to suitable directories. Please do not move or remove them.

At the moment these files are [InjectiveTypes.lagda](InjectiveTypes.lagda) and [InjectiveTypes-article.lagda](InjectiveTypes-article.lagda).

To add more such files, create them, and import them in [Redirection/index.lagda](Redirection/index.lagda).
To check that everything is fine, typecheck [AllModulesIndex.lagda](AllModulesIndex.lagda), which imports [Redirection/index.lagda](Redirection/index.lagda).

The script [updateurl](../updateurl) also implements, in a different way, such a redirection for external links that point to the html rendering. For links to html files, it is enough to update this script.
