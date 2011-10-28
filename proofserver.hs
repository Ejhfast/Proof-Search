module Main where
import Control.Monad (msum)
import Happstack.Server
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import ProofParse

main :: IO ()
main = simpleHTTP nullConf $ app

app :: ServerPart Response
app = do 
  decodeBody (defaultBodyPolicy "/tmp/" (10*10^6) 1000 1000) 
  msum [   dir "checkproof" $ process ]
           
process :: ServerPart Response
process = do 
  methodM POST
  rs <- look "rulesets"
  as <- look "assumptions"
  let rs_parsed = parse rulesets "" rs
  let as_parsed = parse assumptions "" as
  ok $ toResponse $ (show rs_parsed) ++"\n\n"++(show as_parsed)