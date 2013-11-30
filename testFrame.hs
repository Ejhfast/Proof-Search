{-# LANGUAGE TemplateHaskell #-}
 module SomeModule where
 import Test.Framework.TH
 import Test.Framework
 import Test.HUnit
 import Test.Framework.Providers.HUnit
 import Test.Framework.Providers.QuickCheck2

 -- observe this line!
 main = $(defaultMainGenerator)
