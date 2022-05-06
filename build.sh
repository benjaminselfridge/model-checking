cabal build
pandoc --metadata title="Model Checking in Haskell, Part 1: Transition Systems and Invariants" -s --toc --number-sections -o doc/ModelChecking1.md src/ModelChecking1.lhs
pandoc --metadata title="Model Checking in Haskell, Part 1: Transition Systems and Invariants" -s --toc --number-sections -o doc/ModelChecking1.html src/ModelChecking1.lhs
pandoc --metadata title="Model Checking in Haskell, Part 2: From Programs to Transition Systems" -s --toc --number-sections -o doc/ModelChecking2.md src/ModelChecking2.lhs
pandoc --metadata title="Model Checking in Haskell, Part 2: From Programs to Transition Systems" -s --toc --number-sections -o doc/ModelChecking2.html src/ModelChecking2.lhs
