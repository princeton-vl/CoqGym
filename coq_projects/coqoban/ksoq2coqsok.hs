import System
import IO

preamble = "Set Implicit Arguments.\nRequire Export Sokoban.\n\n"

translateChar :: Char -> (Char,Char)
translateChar '#' = ('#','R')
translateChar ' ' = ('-','R')
translateChar '.' = ('O','R')
translateChar '$' = ('x','R')
translateChar '*' = ('@','R')
translateChar '@' = ('+','L')
translateChar '+' = ('%','L')
translateChar x = (x,'R')

processLine [] = ("|> "," <|\n")
processLine (c:cs)
   | c `elem` "# .$*@+" =
       case ((translateChar c),(processLine cs)) of
         ((x,'R'),(y,pcs)) -> (y,(x:' ':pcs))
         ((x,'L'),(y,pcs)) -> ("+> ",(x:' ':pcs))
   | otherwise = processLine cs

processBoard [] = "|><|.\n\n"
processBoard (r:rs) = ((\lp->(fst lp)++(snd lp)) (processLine r))++(processBoard rs)

ksokToCoqsok =  (\(brd,rst) -> (processBoard brd):(ksokToCoqsok (tail (tail rst))))
		   . (break ((==[]) . words))

text = (preamble ++) . concat . (zipWith (\n b -> ("\nDefinition Level_"++(show n)++" :=\n"++b)) [1..])


lines' ""  =  []
lines' s   =  let (l, s') = break (\c-> (c== '\n' || c== '\NUL')) s
               in  l : case s' of
                          []      -> []
                          (_:s'') -> lines' s''

main = do c<-getArgs
	  case c of 
            [x] ->  do  kfile <- openFile x ReadMode
			klevels <- hGetContents kfile
			coqfile <- openFile (x++".v") WriteMode
			hPutStrLn coqfile (text (ksokToCoqsok (lines' klevels)))
	    _ -> return () 
