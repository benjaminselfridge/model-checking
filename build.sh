cabal build

pandoc -s --toc --metadata title="Model Checking in Haskell, Part 1: Transition Systems and Invariants" -f markdown+lhs -t html -c ../css/pandoc.css -o doc/ModelChecking1.html src/ModelChecking1.lhs
pandoc -s --toc --metadata title="Model Checking in Haskell, Part 2: From Programs to Transition Systems" -f markdown+lhs -t html -c ../css/pandoc.css -o doc/ModelChecking2.html src/ModelChecking2.lhs

pandoc -s --metadata title="Model Checking in Haskell, Part 1: Transition Systems and Invariants" -f markdown+lhs -t markdown -o doc/ModelChecking1.md src/ModelChecking1.lhs
pandoc -s --metadata title="Model Checking in Haskell, Part 2: From Programs to Transition Systems" -f markdown+lhs -t markdown -o doc/ModelChecking2.md src/ModelChecking2.lhs
