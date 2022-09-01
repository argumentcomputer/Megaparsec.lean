import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Straume.Coco
import Megaparsec.Common
import Megaparsec.String
import Megaparsec.ParserState

open MonadParsec
open Megaparsec.Parsec
open Straume.Coco
open Megaparsec.Common
open Megaparsec.String
open Megaparsec.ParserState

namespace Megaparsec.Char

universe v

variable (m : Type → Type v) (℘ E : Type) (α : Type := String)
         [MonadParsec m ℘ α E Char] [MonadParsec m ℘ String E Char]
         [Alternative m]

structure Spaces where
  space0020 := ' '
  nbsp00a0 := ' '
  osm1680 := ' '
  mongol180e := '᠎'
  enquad2000 := ' '
  emquad2001 := ' '
  nut2002 := ' '
  mutton2003 := ' '
  thirdemspc2004 := ' '
  fourthemspc2005 := ' '
  sixthemspc20065 := ' '
  figspc2007 := ' '
  puncspc2008 := ' '
  thinspc2009 := ' '
  hairspc200a := ' '
  zwspc200b := '​'
  narrownbsp202f := ' '
  medmathspc205f := ' '
  ideographicspc3000 := '　'
  zwnbspfeff := '﻿'
  each := [ space0020, nbsp00a0, osm1680, mongol180e, enquad2000, emquad2001, nut2002,
            mutton2003, thirdemspc2004, fourthemspc2005, sixthemspc20065, figspc2007, puncspc2008, thinspc2009,
            hairspc200a, zwspc200b, narrownbsp202f, medmathspc205f, ideographicspc3000, zwnbspfeff ]
  visible := [ space0020, nbsp00a0, osm1680, enquad2000, emquad2001, nut2002, mutton2003, thirdemspc2004,
               fourthemspc2005, figspc2007, puncspc2008, thinspc2009, hairspc200a,
               narrownbsp202f, medmathspc205f, ideographicspc3000 ]
  invisible := List.removeAll each visible
  -- TODO
  -- breaking :=
  -- nonbreaking :=
  deriving Inhabited


-- TODO: inline!
-- TODO: vertical tab?!
def isHSpace (x : Char) : Bool :=
  (List.any (default : Spaces).each $ BEq.beq x) || x == '\t'

def isVisibleHSpace (x : Char) : Bool :=
  (List.any (default : Spaces).visible $ BEq.beq x) || x == '\t'

def isInvisibleHSpace (x : Char) : Bool :=
  List.any (default : Spaces).invisible $ BEq.beq x

def isSpace (x : Char) : Bool :=
  isHSpace x || (List.any ['\n', '\r'] $ BEq.beq x)

structure CharSimple where
  char (x : Char) : m Char := single m ℘ E α x
  char' (x : Char) : m Char := choice ℘ α E Char [ char x.toLower, char x.toUpper ]
  anySingle : m Char := anySingle m ℘ α E
  newline := char '\n'
  cr := char '\r'
  crlf : m String := string m ℘ E Char "\r\n"
  eol : m String :=
    MonadParsec.label ℘ α E Char
      "end of line" $
      (newline *> MonadParsec.tokens ℘ E Char (fun _ _ => true) "*") <|> crlf
  eof : m Unit :=
    MonadParsec.eof ℘ α E Char
  noneOf (xs : List Char) := noneOf m ℘ α E xs
  tab : m Char := char '\t'
  hSpace : m String := MonadParsec.takeWhileP ℘ E (.some "horizontal whitespace") isHSpace
  dropHSpace : m Unit := void hSpace
  visibleHSpace : m String := MonadParsec.takeWhileP ℘ E (.some "visible horizontal whitespace") isVisibleHSpace
  dropVisibleHSpace : m Unit := void visibleHSpace
  -- TODO: space doesn't work properly (doesn't consume any input)
  -- Could the bug be in takeWhileP?!
  --
  -- Maybe Inhabited deriving doesn't work properly?
  space : m String := MonadParsec.takeWhileP ℘ E (.some "whitespace") isSpace
  dropSpace : m Unit := void space
  hSpace1 : m String := MonadParsec.takeWhile1P ℘ E (.some "horizontal whitespace") isHSpace
  dropHSpace1 : m Unit := void hSpace1
  visibleHSpace1 : m String := MonadParsec.takeWhile1P ℘ E (.some "visible horizontal whitespace") isVisibleHSpace
  dropVisibleHSpace1 : m Unit := void visibleHSpace1
  space1 : m String := MonadParsec.takeWhile1P ℘ E (.some "whitespace") isSpace
  dropSpace1 : m Unit := void space1

def char_simple (℘x : Type) [MonadParsec (Parsec Char ℘x Unit) ℘x String Unit Char] : CharSimple (Parsec Char ℘x Unit) ℘x Unit := {}
def char_simple_pure : CharSimple (Parsec Char String Unit) String Unit := {}

def char_parsecT (mx : Type → Type v) (℘x : Type)
                 [MonadParsec (ParsecT mx Char ℘x Unit) ℘x String Unit Char]
                 : CharSimple (ParsecT mx Char ℘x Unit) ℘x Unit := {}