cabal build
pandoc -s --metadata title="Model Checking in Haskell, Part 1" -f markdown+lhs -t gfm --markdown-headings=setext -o doc/ModelChecking1.md src/ModelChecking1.lhs
pandoc -s --metadata title="Model Checking in Haskell, Part 1" -f markdown+lhs -t html -o doc/ModelChecking1.html src/ModelChecking1.lhs
pandoc -s --metadata title="Model Checking in Haskell, Part 2" -f markdown+lhs -t gfm --markdown-headings=setext -o doc/ModelChecking2.md src/ModelChecking2.lhs
pandoc -s --metadata title="Model Checking in Haskell, Part 2" -f markdown+lhs -t html -o doc/ModelChecking2.html src/ModelChecking2.lhs
pandoc -s --metadata title="Model Checking in Haskell, Part 3" -f markdown+lhs -t gfm --markdown-headings=setext -o doc/ModelChecking3.md src/ModelChecking3.lhs
pandoc -s --metadata title="Model Checking in Haskell, Part 3" -f markdown+lhs -t html -o doc/ModelChecking3.html src/ModelChecking3.lhs
