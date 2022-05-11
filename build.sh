cabal build
pandoc -s --metadata title="Model Checking in Haskell, Part 1" -f markdown+lhs -t markdown_github+yaml_metadata_block --markdown-headings=setext -o doc/ModelChecking1.md src/ModelChecking1.lhs
pandoc -f markdown+lhs -t html -s -o doc/ModelChecking1.html src/ModelChecking1.lhs
pandoc -f markdown+lhs -t markdown+lhs --markdown-headings=setext -s -o doc/ModelChecking2.md src/ModelChecking2.lhs
pandoc -f markdown+lhs -t html -s -o doc/ModelChecking2.html src/ModelChecking2.lhs
pandoc -f markdown+lhs -t markdown+lhs --markdown-headings=setext -s -o doc/ModelChecking3.md src/ModelChecking3.lhs
pandoc -f markdown+lhs -t html -s -o doc/ModelChecking3.html src/ModelChecking3.lhs
