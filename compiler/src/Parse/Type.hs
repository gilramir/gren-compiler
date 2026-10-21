{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Parse.Type
  ( annotation,
    context,
    expression,
    variant,
  )
where

import AST.Source qualified as Src
import AST.SourceComments qualified as SC
import Data.Name qualified as Name
import Data.Utf8 qualified as Utf8
import Parse.Keyword qualified as Keyword
import Parse.Number qualified as Number
import Parse.Primitives (Parser, addEnd, addLocation, getPosition, inContext, lookAhead, oneOf, oneOfWithFallback, specialize, word1, word2)
import Parse.Primitives qualified as P
import Parse.Symbol qualified as Symbol
import Parse.Space qualified as Space
import Parse.Variable qualified as Var
import Reporting.Annotation qualified as A
import Reporting.Error.Syntax qualified as E

-- TYPE TERMS

term :: Parser E.Type Src.Type
term =
  do
    start <- getPosition
    oneOf
      E.TStart
      [ -- types with no arguments (Int, Float, etc.)
        do
          upper <- Var.foreignUpper E.TStart
          end <- getPosition
          let region = A.Region start end
          return $
            A.At region $
              case upper of
                Var.Unqualified name ->
                  Src.TType region name []
                Var.Qualified home name ->
                  Src.TTypeQual region home name [],
        -- type variables
        do
          var <- Var.lower E.TStart
          addEnd start (Src.TVar var),
        -- parenthesis
        inContext E.TParenthesis (word1 0x28 {-(-} E.TStart) $
          do
            commentsAfterOpeningParen <- Space.chompAndCheckIndent E.TParenthesisSpace E.TParenthesisIndentOpen
            named <- oneOfWithFallback [lookAhead namedHead >> return True] False
            if named
              then namedType start
              else do
                ((tipe, commentsBeforeClosingParen), end) <- specialize E.TParenthesisType expression
                Space.checkIndent end E.TParenthesisIndentEnd
                word1 0x29 {-)-} E.TParenthesisEnd
                let comments = SC.TParensComments commentsAfterOpeningParen commentsBeforeClosingParen
                addEnd start (Src.TParens tipe comments),
        -- records
        inContext E.TRecord (word1 0x7B {- { -} E.TStart) $
          do
            commentsAfterOpenBrace <- Space.chompAndCheckIndent E.TRecordSpace E.TRecordIndentOpen
            oneOf
              E.TRecordOpen
              [ do
                  word1 0x7D {-}-} E.TRecordEnd
                  addEnd start (Src.TRecord [] Nothing),
                do
                  name <- addLocation (Var.lower E.TRecordField)
                  commentsAfterFirstName <- Space.chompAndCheckIndent E.TRecordSpace E.TRecordIndentColon
                  oneOf
                    E.TRecordColon
                    [ do
                        word1 0x7C E.TRecordColon
                        commentsAfterBar <- Space.chompAndCheckIndent E.TRecordSpace E.TRecordIndentField
                        let baseComments = SC.UpdateComments commentsAfterOpenBrace commentsAfterFirstName
                        field <- chompField commentsAfterBar
                        fields <- chompRecordEnd [field]
                        addEnd start (Src.TRecord fields (Just (name, baseComments))),
                      do
                        word1 0x3A {-:-} E.TRecordColon
                        commentsAfterColon <- Space.chompAndCheckIndent E.TRecordSpace E.TRecordIndentType
                        ((tipe, commentsAfterTipe), end) <- specialize E.TRecordType expression
                        Space.checkIndent end E.TRecordIndentEnd
                        let fieldComments = SC.RecordFieldComments commentsAfterOpenBrace commentsAfterFirstName commentsAfterColon commentsAfterTipe
                        let field = (name, tipe, fieldComments)
                        fields <- chompRecordEnd [field]
                        addEnd start (Src.TRecord fields Nothing)
                    ]
              ]
      ]

-- NAMED TYPES

-- | Whether a parenthesis opens a named type: a lowercase name and then a
-- colon. Without the colon it is a parenthesized type that starts with a type
-- variable, @(a -> b)@, so this is only looked at, never consumed.
namedHead :: Parser E.TParenthesis ()
namedHead =
  do
    _ <- Var.lower E.TParenthesisEnd
    _ <- Space.chomp E.TParenthesisSpace
    word1 0x3A {-:-} E.TParenthesisEnd

-- | @(name : Type)@ or @(name : Type where predicate)@ (geng-lang
-- @m4-refine.md@ D814), after its @(@.
namedType :: A.Position -> Parser E.TParenthesis Src.Type
namedType start =
  do
    name <- addLocation (Var.lower E.TParenthesisEnd)
    _ <- Space.chompAndCheckIndent E.TParenthesisSpace E.TParenthesisIndentEnd
    word1 0x3A {-:-} E.TParenthesisEnd
    _ <- Space.chompAndCheckIndent E.TParenthesisSpace E.TParenthesisIndentOpen
    ((tipe, _), end) <- specialize E.TParenthesisType expression
    Space.checkIndent end E.TParenthesisIndentEnd
    maybePredicate <-
      oneOfWithFallback
        [ do
            Keyword.where_ E.TParenthesisEnd
            _ <- Space.chompAndCheckIndent E.TParenthesisSpace E.TParenthesisPredicate
            (predicate, predicateEnd, text) <- withText chain
            Space.checkIndent predicateEnd E.TParenthesisIndentEnd
            return (Just (predicate, text))
        ]
        Nothing
    word1 0x29 {-)-} E.TParenthesisEnd
    addEnd start (Src.TNamed name tipe maybePredicate)

-- PREDICATES

-- | A predicate and its source text (D812): the bytes from where the parser
-- started to the end of the predicate's region, so the whitespace and
-- comments a chain chomps after its last operand are not in it. The bytes are
-- copied while the parse holds the source.
withText :: Parser x (Src.Expr, A.Position) -> Parser x (Src.Expr, A.Position, String)
withText (P.Parser parser) =
  P.Parser $ \state@(P.State _ start _ _ row col) cok eok cerr eerr ->
    let finish ok (predicate, end) s@(P.State _ stop _ _ _ _) =
          let !bytes = Utf8.fromPtr start stop :: Utf8.Utf8 ()
           in ok (predicate, end, upTo (A.Position row col) (regionEnd predicate) (Utf8.toChars bytes)) s
     in parser state (finish cok) (finish eok) cerr eerr
  where
    regionEnd (A.At (A.Region _ end) _) = end

-- | The characters from one position up to another, counting a column a
-- character and a row a newline, as the parser counts them.
upTo :: A.Position -> A.Position -> String -> String
upTo here@(A.Position r c) end chars =
  case chars of
    ch : rest
      | here /= end ->
          ch : upTo (if ch == '\n' then A.Position (r + 1) 1 else A.Position r (c + 1)) end rest
    _ -> []

-- | A refinement's predicate, read by its own grammar rather than by the
-- expression parser, which imports this module (D815). It holds what D808
-- allows: integer literals, names, a qualified function applied to one name
-- (a measure, @Bytes.length b@), @True@, @False@, @not@, unary @-@, the
-- operators @+ - * < <= > >= == /= && ||@ and parentheses.
--
-- The operators are read as a chain, @Src.Binops@, as the expression parser
-- reads them, and canonicalization gives them their precedence, so a predicate
-- is the expression it would be anywhere else. That @a < b < c@ does not
-- type, or that a @*@ needs a literal side, is for the checker to say.
chain :: Parser E.TParenthesis (Src.Expr, A.Position)
chain =
  do
    start <- getPosition
    (first, firstEnd) <- operand
    chainHelp start [] first firstEnd

chainHelp :: A.Position -> [Src.BinopsSegment] -> Src.Expr -> A.Position -> Parser E.TParenthesis (Src.Expr, A.Position)
chainHelp start ops current currentEnd =
  do
    -- Chomped outside the choice, as `expression` chomps before its `->`:
    -- a chomp succeeds as having consumed, so inside it the `)` that ends
    -- the predicate would be an error rather than the end.
    commentsBefore <- Space.chomp E.TParenthesisSpace
    chainOperator start ops current currentEnd commentsBefore

chainOperator :: A.Position -> [Src.BinopsSegment] -> Src.Expr -> A.Position -> [Src.Comment] -> Parser E.TParenthesis (Src.Expr, A.Position)
chainOperator start ops current currentEnd commentsBefore =
  oneOfWithFallback
    [ do
        Space.checkIndent currentEnd E.TParenthesisIndentEnd
        opStart <- getPosition
        op <- Symbol.operator E.TParenthesisPredicate (\_ -> E.TParenthesisPredicate)
        opEnd <- getPosition
        if op `elem` predicateOperators
          then return ()
          else refuseAt opStart
        commentsAfter <- Space.chompAndCheckIndent E.TParenthesisSpace E.TParenthesisPredicate
        (next, nextEnd) <- operand
        let segment = (current, A.At (A.Region opStart opEnd) op, SC.BinopsSegmentComments commentsBefore commentsAfter)
        chainHelp start (segment : ops) next nextEnd
    ]
    (finish start ops current currentEnd, currentEnd)
  where
    finish s revOps lastExpr end =
      case revOps of
        [] -> lastExpr
        _ -> A.at s end (Src.Binops (reverse revOps) lastExpr)

predicateOperators :: [Name.Name]
predicateOperators =
  map Name.fromChars ["+", "-", "*", "<", "<=", ">", ">=", "==", "/=", "&&", "||"]

operand :: Parser E.TParenthesis (Src.Expr, A.Position)
operand =
  do
    start <- getPosition
    oneOf
      E.TParenthesisPredicate
      [ do
          word1 0x28 {-(-} E.TParenthesisPredicate
          commentsAfterOpen <- Space.chompAndCheckIndent E.TParenthesisSpace E.TParenthesisPredicate
          (inner, innerEnd) <- chain
          commentsBeforeClose <- Space.chompAndCheckIndent E.TParenthesisSpace E.TParenthesisIndentEnd
          Space.checkIndent innerEnd E.TParenthesisIndentEnd
          word1 0x29 {-)-} E.TParenthesisEnd
          end <- getPosition
          return (A.at start end (Src.Parens commentsAfterOpen inner commentsBeforeClose), end),
        do
          word1 0x2D {---} E.TParenthesisPredicate
          (inner, end) <- operand
          return (A.at start end (Src.Negate inner), end),
        do
          nmbr <- Number.number E.TParenthesisPredicate (\_ -> E.TParenthesisPredicate)
          end <- getPosition
          case nmbr of
            Number.Int int intFormat ->
              return (A.at start end (Src.Int int intFormat), end)
            Number.Float _ ->
              refuseAt start,
        do
          var <- Var.foreignAlpha E.TParenthesisPredicate
          end <- getPosition
          let func = A.at start end var
          case var of
            Src.Var Src.LowVar name
              | name == Name.fromChars "not" ->
                  do
                    comments <- Space.chompAndCheckIndent E.TParenthesisSpace E.TParenthesisPredicate
                    (arg, argEnd) <- operand
                    return (A.at start argEnd (Src.Call func [(comments, arg)]), argEnd)
              | otherwise ->
                  return (func, end)
            Src.Var Src.CapVar name
              | name == Name.fromChars "True" || name == Name.fromChars "False" ->
                  return (func, end)
            Src.VarQual Src.LowVar _ _ ->
              do
                comments <- Space.chompAndCheckIndent E.TParenthesisSpace E.TParenthesisPredicate
                argStart <- getPosition
                argName <- Var.lower E.TParenthesisPredicate
                argEnd <- getPosition
                let arg = A.at argStart argEnd (Src.Var Src.LowVar argName)
                return (A.at start argEnd (Src.Call func [(comments, arg)]), argEnd)
            _ ->
              refuseAt start
      ]

-- | A predicate holds something D808 does not allow: an operator outside its
-- list, a float, a constructor other than @True@ and @False@.
refuseAt :: A.Position -> Parser E.TParenthesis a
refuseAt (A.Position row col) =
  P.Parser $ \_ _ _ cerr _ -> cerr row col E.TParenthesisPredicate

-- ANNOTATIONS

-- | A type, optionally qualified by a constraint context: @Eq a => a -> Bool@.
--
-- The context has to be recognized before it can be parsed, because both of
-- its shapes are already something else. @Eq a@ is a perfectly good type, and
-- @(@ opens a parenthesized type as readily as a multi-constraint list; the
-- only thing that separates them is the @=>@ several tokens later, and by then
-- an ordinary `oneOf` has committed. So the context is parsed once under
-- `lookAhead` to find out whether there is one at all, and then parsed again
-- for real. It is at most a handful of tokens and it happens once per
-- annotation.
--
-- The cost of that shape, worth knowing: a *malformed* context is not a
-- context, so @(Eq a, Ord) => …@ rewinds and is reported as a bad type rather
-- than as a bad constraint. The error is in the right place and says the wrong
-- thing, which is the trade for having no committed prefix to report from.
annotation :: Space.Parser E.Type (Maybe Src.Context, Src.Type, [Src.Comment])
annotation =
  do
    maybeContext <-
      oneOfWithFallback
        [ do
            _ <- lookAhead context
            Just <$> context
        ]
        Nothing
    ((tipe, commentsAfter), end) <- expression
    return ((maybeContext, tipe, commentsAfter), end)

context :: Parser E.Type Src.Context
context =
  do
    (entries, commentsBeforeArrow) <-
      oneOf
        E.TStart
        [ do
            word1 0x28 {-(-} E.TStart
            commentsAfterOpen <- Space.chompAndCheckIndent E.TSpace E.TIndentStart
            entries <- chompContextEntries commentsAfterOpen []
            commentsAfterClose <- Space.chompAndCheckIndent E.TSpace E.TIndentStart
            return (entries, commentsAfterClose),
          do
            entry <- chompConstraint []
            return ([entry], [])
        ]
    word2 0x3D 0x3E {-=>-} E.TStart
    commentsAfterArrow <- Space.chompAndCheckIndent E.TSpace E.TIndentStart
    return (Src.Context entries (SC.ContextComments commentsBeforeArrow commentsAfterArrow))

chompContextEntries :: [Src.Comment] -> [Src.ContextEntry] -> Parser E.Type [Src.ContextEntry]
chompContextEntries commentsBefore revEntries =
  do
    entry <- chompConstraint commentsBefore
    oneOf
      E.TStart
      [ do
          word1 0x2C {-,-} E.TStart
          commentsAfterComma <- Space.chompAndCheckIndent E.TSpace E.TIndentStart
          chompContextEntries commentsAfterComma (entry : revEntries),
        do
          word1 0x29 {-)-} E.TStart
          return (reverse (entry : revEntries))
      ]

-- | @Eq a@ — a class applied to a type variable, and only to a variable. An
-- argument that is not a variable is an instance head rather than a
-- constraint, and there is nowhere for it to go: D111 keys the constraint list
-- off the annotation's bound variables.
chompConstraint :: [Src.Comment] -> Parser E.Type Src.ContextEntry
chompConstraint commentsBefore =
  do
    start <- getPosition
    upper <- Var.foreignUpper E.TStart
    commentsAfterClass <- Space.chompAndCheckIndent E.TSpace E.TIndentStart
    var <- addLocation (Var.lower E.TStart)
    end <- getPosition
    commentsAfter <- Space.chomp E.TSpace
    let region = A.Region start end
    let constraint =
          case upper of
            Var.Unqualified name ->
              Src.Constraint region name var
            Var.Qualified home name ->
              Src.ConstraintQual region home name var
    return
      ( A.At region constraint,
        SC.ConstraintComments commentsBefore commentsAfterClass commentsAfter
      )

-- TYPE EXPRESSIONS

expression :: Space.Parser E.Type (Src.Type, [Src.Comment])
expression =
  do
    start <- getPosition
    term1@((tipe1, commentsBeforeArrow), end1) <-
      oneOf
        E.TStart
        [ app start,
          do
            eterm <- term
            end <- getPosition
            commentsAfter <- Space.chomp E.TSpace
            return ((eterm, commentsAfter), end)
        ]
    oneOfWithFallback
      [ do
          Space.checkIndent end1 E.TIndentStart -- should never trigger
          word2 0x2D 0x3E {-->-} E.TStart -- could just be another type instead
          commentsAfterArrow <- Space.chompAndCheckIndent E.TSpace E.TIndentStart
          ((tipe2, commentsAfter), end2) <- expression
          let comments = SC.TLambdaComments commentsBeforeArrow commentsAfterArrow
          let tipe = A.at start end2 (Src.TLambda tipe1 tipe2 comments)
          return ((tipe, commentsAfter), end2)
      ]
      term1

-- TYPE CONSTRUCTORS

app :: A.Position -> Space.Parser E.Type (Src.Type, [Src.Comment])
app start =
  do
    upper <- Var.foreignUpper E.TStart
    upperEnd <- getPosition
    commentsAfterUpper <- Space.chomp E.TSpace
    ((args, commentsAfterArgs), end) <- chompArgs [] commentsAfterUpper upperEnd

    let region = A.Region start upperEnd
    let tipe =
          case upper of
            Var.Unqualified name ->
              Src.TType region name args
            Var.Qualified home name ->
              Src.TTypeQual region home name args

    return ((A.at start end tipe, commentsAfterArgs), end)

chompArgs :: [([Src.Comment], Src.Type)] -> [Src.Comment] -> A.Position -> Space.Parser E.Type ([([Src.Comment], Src.Type)], [Src.Comment])
chompArgs args commentsBetween end =
  oneOfWithFallback
    [ do
        Space.checkIndent end E.TIndentStart
        arg <- term
        newEnd <- getPosition
        commentsAfter <- Space.chomp E.TSpace
        chompArgs ((commentsBetween, arg) : args) commentsAfter newEnd
    ]
    ((reverse args, commentsBetween), end)

-- RECORD

chompRecordEnd :: [Src.TRecordField] -> Parser E.TRecord [Src.TRecordField]
chompRecordEnd fields =
  oneOf
    E.TRecordEnd
    [ do
        word1 0x2C {-,-} E.TRecordEnd
        commentsAfterComma <- Space.chompAndCheckIndent E.TRecordSpace E.TRecordIndentField
        field <- chompField commentsAfterComma
        chompRecordEnd (field : fields),
      do
        word1 0x7D {-}-} E.TRecordEnd
        return (reverse fields)
    ]

chompField :: [Src.Comment] -> Parser E.TRecord Src.TRecordField
chompField commentsBefore =
  do
    name <- addLocation (Var.lower E.TRecordField)
    commentsAfterName <- Space.chompAndCheckIndent E.TRecordSpace E.TRecordIndentColon
    word1 0x3A {-:-} E.TRecordColon
    commentsAfterColon <- Space.chompAndCheckIndent E.TRecordSpace E.TRecordIndentType
    ((tipe, commentsAfterTipe), end) <- specialize E.TRecordType expression
    Space.checkIndent end E.TRecordIndentEnd
    let comments = SC.RecordFieldComments commentsBefore commentsAfterName commentsAfterColon commentsAfterTipe
    return (name, tipe, comments)

-- VARIANT

variant :: Space.Parser E.CustomType (A.Located Name.Name, [([Src.Comment], Src.Type)], [Src.Comment])
variant =
  do
    name@(A.At (A.Region _ nameEnd) _) <- addLocation (Var.upper E.CT_Variant)
    commentsBefore <- Space.chomp E.CT_Space
    ((args, commentsAfter), end) <- specialize E.CT_VariantArg (chompArgs [] commentsBefore nameEnd)
    return ((name, args, commentsAfter), end)
