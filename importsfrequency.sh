# Frequency table of `open imports`

grep "open import" `git ls-files '*agda'` --no-filename \
    | sed 's/^[ \t]*//'                                 \
    | sed 's/open import //'                            \
    | sed 's/ .*//'                                     \
    | sort                                              \
    | uniq -c                                           \
    | sort -r

# sed (1) removes all spaces at the beginning of a line.
# sed (2) removes "open import ".
# sed (3) removes the first space " " and everything that follows it.
