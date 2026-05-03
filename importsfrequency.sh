# Frequency table of `open imports`

grep "open import" `git ls-files '*agda'` --no-filename | sed 's/^[ \t]*//' | sort | uniq -c | sort -r
