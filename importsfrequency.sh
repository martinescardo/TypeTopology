# Frequency table of `open imports`

grep "open import" `git ls-files '*agda'` --no-filename | sed 's/^[ \t]*//' | sort | uniq -c | sort -r

# sed is used to remove all spaces at the beginning of a line
