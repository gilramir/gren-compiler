-- Temporary while implementing gren format
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Parse.Declaration
  ( Decl (..),
    declaration,
    infix_,
  )
where

import AST.Source qualified as Src
import AST.SourceComments qualified as SC
import AST.Utils.Binop qualified as Binop
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Name qualified as Name
import Parse.Expression qualified as Expr
import Parse.Keyword qualified as Keyword
import Parse.Number qualified as Number
import Parse.Pattern qualified as Pattern
import Parse.Primitives hiding (State)
import Parse.Primitives qualified as P
import Parse.Space qualified as Space
import Parse.Symbol qualified as Symbol
import Parse.Type qualified as Type
import Parse.Variable qualified as Var
import Reporting.Annotation qualified as A
import Reporting.Error.Syntax qualified as E

-- DECLARATION

data Decl
  = Value (Maybe Src.DocComment) (A.Located Src.Value)
  | Class (Maybe Src.DocComment) (A.Located Src.Class)
  | Instance (Maybe Src.DocComment) (A.Located Src.Instance)
  | Union (Maybe Src.DocComment) (A.Located Src.Union)
  | Alias (Maybe Src.DocComment) (A.Located Src.Alias)
  | Port (Maybe Src.DocComment) Src.Port
  | TopLevelComments (NonEmpty Src.Comment)
  deriving (Show)

declaration :: Space.Parser E.Decl (Decl, [Src.Comment])
declaration =
  do
    maybeDocs <- chompDocComment
    derives <- chompDerive
    start <- getPosition
    case derives of
      Just classes ->
        -- `@derive` says which classes an abstract type derives (D53,
        -- `classes.md` §8.1), so the declaration it is attached to has to be a
        -- custom type. Anything else is a misplaced attribute rather than a
        -- declaration that quietly ignores it. The fallback only fires when
        -- `type` is absent, so a real error *inside* the type declaration is
        -- still reported as itself.
        oneOf
          E.DeclStart
          [ typeDecl maybeDocs start classes,
            attributeNotOnCustomType
          ]
      Nothing ->
        oneOf
          E.DeclStart
          [ typeDecl maybeDocs start [],
            portDecl maybeDocs,
            classDecl maybeDocs start,
            instanceDecl maybeDocs start,
            valueDecl maybeDocs start
          ]

-- ATTRIBUTES

-- | @\@derive(Eq, Ord, Inspect)@ on the line before a custom type.
--
-- Nothing in the parser handled @\@@ before this; `ffi.md` F1's @\@extern@ is
-- the other customer and will land beside it. An attribute follows the doc
-- comment and precedes the declaration, which is the order Rust and Gren's own
-- doc comments already read in.
chompDerive :: Parser E.Decl (Maybe [A.Located Name.Name])
chompDerive =
  oneOfWithFallback
    [ inContext E.DeclAttribute (word1 0x40 {-\@-} E.DeclStart) $
        do
          name <- Var.lower E.AttributeName
          nameEnd <- getPosition
          if name /= Name.fromChars "derive"
            then attributeUnknown name nameEnd
            else return ()
          Space.chompAndCheckIndent E.AttributeSpace E.AttributeIndentOpen
          word1 0x28 {-(-} E.AttributeOpen
          Space.chompAndCheckIndent E.AttributeSpace E.AttributeIndentClass
          classes <- chompDeriveClasses []
          Space.chomp E.AttributeSpace
          Space.checkFreshLine E.AttributeIndentDecl
          return (Just classes)
    ]
    Nothing

attributeNotOnCustomType :: Space.Parser E.Decl (Decl, [Src.Comment])
attributeNotOnCustomType =
  P.Parser $ \(P.State _ _ _ _ row col) _ _ cerr _ ->
    cerr row col (E.DeclAttribute (E.AttributeNotOnCustomType row col))

attributeUnknown :: Name.Name -> A.Position -> Parser E.Attribute ()
attributeUnknown name (A.Position row col) =
  P.Parser $ \_ _ _ cerr _ -> cerr row col (E.AttributeUnknown name)

chompDeriveClasses :: [A.Located Name.Name] -> Parser E.Attribute [A.Located Name.Name]
chompDeriveClasses revClasses =
  do
    class_ <- addLocation (Var.upper E.AttributeClass)
    Space.chompAndCheckIndent E.AttributeSpace E.AttributeIndentEnd
    oneOf
      E.AttributeEnd
      [ do
          word1 0x2C {-,-} E.AttributeEnd
          Space.chompAndCheckIndent E.AttributeSpace E.AttributeIndentClass
          chompDeriveClasses (class_ : revClasses),
        do
          word1 0x29 {-)-} E.AttributeEnd
          return (reverse (class_ : revClasses))
      ]

-- DOC COMMENT

chompDocComment :: Parser E.Decl (Maybe Src.DocComment)
chompDocComment =
  oneOfWithFallback
    [ do
        docComment <- Space.docComment E.DeclStart E.DeclSpace
        Space.chomp E.DeclSpace
        Space.checkFreshLine E.DeclFreshLineAfterDocComment
        return (Just docComment)
    ]
    Nothing

-- DEFINITION and ANNOTATION

valueDecl :: Maybe Src.DocComment -> A.Position -> Space.Parser E.Decl (Decl, [Src.Comment])
valueDecl maybeDocs start =
  do
    name <- Var.lower E.DeclStart
    end <- getPosition
    specialize (E.DeclDef name) $
      do
        commentsAfterName <- Space.chompAndCheckIndent E.DeclDefSpace E.DeclDefIndentEquals
        oneOf
          E.DeclDefEquals
          [ do
              word1 0x3A {-:-} E.DeclDefEquals
              let commentsBeforeColon = commentsAfterName
              commentsAfterColon <- Space.chompAndCheckIndent E.DeclDefSpace E.DeclDefIndentType
              ((maybeContext, tipe, commentsAfterTipe), _) <- specialize E.DeclDefType Type.annotation
              Space.checkFreshLine E.DeclDefNameRepeat
              defName <- chompMatchingName name
              commentsAfterMatchingName <- Space.chompAndCheckIndent E.DeclDefSpace E.DeclDefIndentEquals
              let tipeComments = SC.ValueTypeComments commentsBeforeColon commentsAfterColon commentsAfterTipe
              chompDefArgsAndBody maybeDocs start defName (Just (Src.Annotation maybeContext tipe tipeComments)) [] commentsAfterMatchingName,
            chompDefArgsAndBody maybeDocs start (A.at start end name) Nothing [] commentsAfterName
          ]

chompDefArgsAndBody :: Maybe Src.DocComment -> A.Position -> A.Located Name.Name -> Maybe Src.Annotation -> [([Src.Comment], Src.Pattern)] -> [Src.Comment] -> Space.Parser E.DeclDef (Decl, [Src.Comment])
chompDefArgsAndBody maybeDocs start name tipe revArgs commentsBefore =
  oneOf
    E.DeclDefEquals
    [ do
        arg <- specialize E.DeclDefArg Pattern.term
        commentsAfterArg <- Space.chompAndCheckIndent E.DeclDefSpace E.DeclDefIndentEquals
        chompDefArgsAndBody maybeDocs start name tipe ((commentsBefore, arg) : revArgs) commentsAfterArg,
      do
        word1 0x3D {-=-} E.DeclDefEquals
        commentsAfterEquals <- Space.chompAndCheckIndent E.DeclDefSpace E.DeclDefIndentBody
        ((body, commentsAfter), end) <- specialize E.DeclDefBody Expr.expression
        let (commentsAfterBody, commentsAfterDef) = List.span (A.isIndentedMoreThan 1) commentsAfter
        let comments = SC.ValueComments commentsBefore commentsAfterEquals commentsAfterBody
        let value = Src.Value name (reverse revArgs) body tipe comments
        let avalue = A.at start end value
        return ((Value maybeDocs avalue, commentsAfterDef), end)
    ]

chompMatchingName :: Name.Name -> Parser E.DeclDef (A.Located Name.Name)
chompMatchingName expectedName =
  let (P.Parser parserL) = Var.lower E.DeclDefNameRepeat
   in P.Parser $ \state@(P.State _ _ _ _ sr sc) cok eok cerr eerr ->
        let cokL name newState@(P.State _ _ _ _ er ec) =
              if expectedName == name
                then cok (A.At (A.Region (A.Position sr sc) (A.Position er ec)) name) newState
                else cerr sr sc (E.DeclDefNameMatch name)

            eokL name newState@(P.State _ _ _ _ er ec) =
              if expectedName == name
                then eok (A.At (A.Region (A.Position sr sc) (A.Position er ec)) name) newState
                else eerr sr sc (E.DeclDefNameMatch name)
         in parserL state cokL eokL cerr eerr

-- CLASS DECLARATIONS

-- | @class Eq a where@ and the annotations under it, or @class Num a@ alone.
--
-- `class` is a contextual keyword (D117), so this has to establish that the
-- declaration really is one before committing to it: `class` followed by an
-- upper-case name is a class, and `class` followed by anything else is a value
-- named `class`, which `Html.Attributes` and `Svg.Attributes` both are. The
-- test is the whole head, read once under `lookAhead` and then read again for
-- real, which is the same shape `Parse.Type.annotation` uses and for the same
-- reason.
--
-- __The body is optional__ (D133). A class with no methods is not a degenerate
-- case to be tolerated: `classes.md` §1.2's closed classes have none — their
-- membership is a table in "Type.Class" and there is nothing for an instance to
-- implement — and `core` has to be able to write `class Num a` for the
-- constraint to be nameable at all. §1.2 writes it that way itself.
--
-- The same `lookAhead` does the work again: `where` is read once without
-- committing, so a declaration that has no body ends at its variable and the
-- space after it belongs to whatever comes next. Its cost is the same one
-- §G14 already pays -- a misindented `where` is now "no body" rather than an
-- indentation error.
classDecl :: Maybe Src.DocComment -> A.Position -> Space.Parser E.Decl (Decl, [Src.Comment])
classDecl maybeDocs start =
  do
    _ <- lookAhead classDeclAhead
    inContext E.DeclClass (Keyword.class_ E.DeclStart) $
      do
        commentsAfterKeyword <- Space.chompAndCheckIndent E.ClassSpace E.ClassIndentName
        name <- addLocation (Var.upper E.ClassName)
        commentsAfterName <- Space.chompAndCheckIndent E.ClassSpace E.ClassIndentVar
        var@(A.At (A.Region _ varEnd) _) <- addLocation (Var.lower E.ClassVar)
        ((methods, commentsAfterVar, commentsAfterWhere, commentsAfter), end) <-
          oneOfWithFallback
            [ do
                _ <- lookAhead classBodyAhead
                afterVar <- Space.chompAndCheckIndent E.ClassSpace E.ClassIndentWhere
                Keyword.where_ E.ClassWhere
                afterWhere <- Space.chompAndCheckIndent E.ClassSpace E.ClassIndentBody
                ((ms, after), bodyEnd) <-
                  withIndent $
                    do
                      ((method, commentsAfterMethod), methodEnd) <- chompClassMethod []
                      chompClassMethods (NonEmpty.singleton method) commentsAfterMethod methodEnd
                return ((ms, afterVar, afterWhere, after), bodyEnd)
            ]
            (([], [], [], []), varEnd)
        let comments = SC.ClassComments commentsAfterKeyword commentsAfterName commentsAfterVar commentsAfterWhere
        let class_ = A.at start end (Src.Class name var methods comments)
        return ((Class maybeDocs class_, commentsAfter), end)

-- | `class` and then an upper-case name, consumed and thrown away by
-- `lookAhead` so that only a real class declaration commits.
classDeclAhead :: Parser E.Decl ()
classDeclAhead =
  do
    Keyword.class_ E.DeclStart
    Space.chompAndCheckIndent E.DeclSpace E.DeclStart
    _ <- Var.upper E.DeclStart
    return ()

-- | `where`, after the class variable, read without committing so that a class
-- with no body is not an indentation error.
classBodyAhead :: Parser E.DeclClass ()
classBodyAhead =
  do
    _ <- Space.chompAndCheckIndent E.ClassSpace E.ClassIndentWhere
    Keyword.where_ E.ClassWhere

chompClassMethods :: NonEmpty Src.ClassMethod -> [Src.Comment] -> A.Position -> Space.Parser E.DeclClass ([Src.ClassMethod], [Src.Comment])
chompClassMethods methods@(lastMethod :| rest) commentsBefore end =
  oneOfWithFallback
    [ do
        Space.checkAligned E.ClassMethodAlignment
        ((method, commentsAfter), newEnd) <- chompClassMethod commentsBefore
        chompClassMethods (NonEmpty.cons method methods) commentsAfter newEnd
    ]
    ( let (commentsAfterLastMethod, commentsAfter) = List.span (A.isIndentedMoreThan 1) commentsBefore
       in ((reverse (withTrailingComments lastMethod commentsAfterLastMethod : rest), commentsAfter), end)
    )

-- | The comments after the last method belong to it when they are indented
-- under the class, and to whatever follows the declaration when they are not
-- -- the same split `chompVariants` makes for a custom type's last variant.
withTrailingComments :: Src.ClassMethod -> [Src.Comment] -> Src.ClassMethod
withTrailingComments (commentsBefore, name, Src.Annotation context tipe typeComments) trailing =
  ( commentsBefore,
    name,
    Src.Annotation context tipe typeComments {SC._afterValueType = trailing}
  )

chompClassMethod :: [Src.Comment] -> Space.Parser E.DeclClass (Src.ClassMethod, [Src.Comment])
chompClassMethod commentsBefore =
  do
    name@(A.At _ methodName) <- addLocation (Var.lower E.ClassMethodName)
    commentsAfterName <- Space.chompAndCheckIndent E.ClassSpace E.ClassIndentMethodColon
    word1 0x3A {-:-} E.ClassMethodColon
    commentsAfterColon <- Space.chompAndCheckIndent E.ClassSpace E.ClassIndentMethodType
    ((maybeContext, tipe, commentsAfterTipe), end) <- specialize (E.ClassMethodType methodName) Type.annotation
    let typeComments = SC.ValueTypeComments commentsAfterName commentsAfterColon []
    return (((commentsBefore, name, Src.Annotation maybeContext tipe typeComments), commentsAfterTipe), end)

-- INSTANCE DECLARATIONS

-- | @instance Eq a => Eq (Array a) where@ and the definitions under it.
--
-- The head is parsed by `Type.annotation`, which is not a shortcut: an
-- instance head *is* an annotation's shape — an optional context and then a
-- type — and `Eq (Array a)` is a type expression whether or not `Eq` turns out
-- to name a class. Asking the parser to split it into a class and an argument
-- would be asking it a question only the environment can answer, and the
-- resolver would have to ask it again.
--
-- `instance` is contextual (D117), so the same `lookAhead` guard `classDecl`
-- uses applies here.
instanceDecl :: Maybe Src.DocComment -> A.Position -> Space.Parser E.Decl (Decl, [Src.Comment])
instanceDecl maybeDocs start =
  do
    _ <- lookAhead instanceDeclAhead
    inContext E.DeclInstance (Keyword.instance_ E.DeclStart) $
      do
        commentsAfterKeyword <- Space.chompAndCheckIndent E.InstanceSpace E.InstanceIndentHead
        ((maybeContext, head_, commentsAfterHead), _) <- specialize E.InstanceHead Type.annotation
        Keyword.where_ E.InstanceWhere
        commentsAfterWhere <- Space.chompAndCheckIndent E.InstanceSpace E.InstanceIndentBody
        ((methods, commentsAfter), end) <-
          withIndent $
            do
              ((method, commentsAfterMethod), methodEnd) <- chompInstanceMethod []
              chompInstanceMethods [method] commentsAfterMethod methodEnd
        let comments = SC.InstanceComments commentsAfterKeyword commentsAfterHead commentsAfterWhere
        let instance_ = A.at start end (Src.Instance maybeContext head_ methods comments)
        return ((Instance maybeDocs instance_, commentsAfter), end)

instanceDeclAhead :: Parser E.Decl ()
instanceDeclAhead =
  do
    Keyword.instance_ E.DeclStart
    Space.chompAndCheckIndent E.DeclSpace E.DeclStart
    _ <- Var.upper E.DeclStart
    return ()

chompInstanceMethods :: [Src.InstanceMethod] -> [Src.Comment] -> A.Position -> Space.Parser E.DeclInstance ([Src.InstanceMethod], [Src.Comment])
chompInstanceMethods revMethods commentsBefore end =
  oneOfWithFallback
    [ do
        Space.checkAligned E.InstanceMethodAlignment
        ((method, commentsAfter), newEnd) <- chompInstanceMethod commentsBefore
        chompInstanceMethods (method : revMethods) commentsAfter newEnd
    ]
    ((reverse revMethods, commentsBefore), end)

chompInstanceMethod :: [Src.Comment] -> Space.Parser E.DeclInstance (Src.InstanceMethod, [Src.Comment])
chompInstanceMethod commentsBefore =
  do
    start <- getPosition
    name <- addLocation (Var.lower E.InstanceMethodName)
    commentsAfterName <- Space.chompAndCheckIndent E.InstanceSpace E.InstanceIndentMethodEquals
    chompInstanceMethodArgs start name commentsBefore [] commentsAfterName

chompInstanceMethodArgs :: A.Position -> A.Located Name.Name -> [Src.Comment] -> [([Src.Comment], Src.Pattern)] -> [Src.Comment] -> Space.Parser E.DeclInstance (Src.InstanceMethod, [Src.Comment])
chompInstanceMethodArgs start@(A.Position _ startCol) name@(A.At _ methodName) commentsBefore revArgs commentsAfterPrev =
  oneOf
    E.InstanceMethodEquals
    [ do
        arg <- specialize E.InstanceMethodArg Pattern.term
        commentsAfterArg <- Space.chompAndCheckIndent E.InstanceSpace E.InstanceIndentMethodEquals
        chompInstanceMethodArgs start name commentsBefore ((commentsAfterPrev, arg) : revArgs) commentsAfterArg,
      do
        word1 0x3D {-=-} E.InstanceMethodEquals
        commentsAfterEquals <- Space.chompAndCheckIndent E.InstanceSpace E.InstanceIndentMethodBody
        ((body, commentsAfter), end) <- specialize (E.InstanceMethodBody methodName) Expr.expression
        let (commentsAfterBody, commentsAfterMethod) = List.span (A.isIndentedMoreThan startCol) commentsAfter
        let comments = SC.ValueComments commentsAfterPrev commentsAfterEquals commentsAfterBody
        let value = A.at start end (Src.Value name (reverse revArgs) body Nothing comments)
        return (((commentsBefore, value), commentsAfterMethod), end)
    ]

-- TYPE DECLARATIONS

typeDecl :: Maybe Src.DocComment -> A.Position -> [A.Located Name.Name] -> Space.Parser E.Decl (Decl, [Src.Comment])
typeDecl maybeDocs start derives =
  inContext E.DeclType (Keyword.type_ E.DeclStart) $
    do
      commentsAfterTypeKeyword <- Space.chompAndCheckIndent E.DT_Space E.DT_IndentName
      oneOf
        E.DT_Name
        [ inContext E.DT_Alias (Keyword.alias_ E.DT_Name) $
            do
              -- A type alias is transparent, so whatever it stands for already
              -- derives structurally and `@derive` on one is the redundancy
              -- `classes.md` §8.1 calls an error rather than a no-op.
              aliasTakesNoAttribute derives
              -- TODO: use commentsAfterTypeKeyword
              Space.chompAndCheckIndent E.AliasSpace E.AliasIndentEquals
              (name, args) <- chompAliasNameToEquals
              ((tipe, commentsAfterTipe), end) <- specialize E.AliasBody Type.expression
              let alias = A.at start end (Src.Alias name args tipe)
              return ((Alias maybeDocs alias, commentsAfterTipe), end),
          specialize E.DT_Union $
            do
              (name, args, commentsAfterArgs, commentsAfterEquals) <- chompCustomNameToEquals
              ((firstName, firstArgs, commentsAfterFirst), firstEnd) <- Type.variant
              let firstVariant = (commentsAfterEquals, firstName, firstArgs, commentsAfterFirst)
              ((variants, commentsAfter), end) <- chompVariants (NonEmpty.singleton firstVariant) firstEnd
              let comments = SC.UnionComments commentsAfterTypeKeyword commentsAfterArgs
              let union = A.at start end (Src.Union name args variants derives comments)
              return ((Union maybeDocs union, commentsAfter), end)
        ]

aliasTakesNoAttribute :: [A.Located Name.Name] -> Parser E.TypeAlias ()
aliasTakesNoAttribute derives =
  case derives of
    [] ->
      P.Parser $ \state _ eok _ _ -> eok () state
    _ : _ ->
      P.Parser $ \(P.State _ _ _ _ row col) _ _ cerr _ ->
        cerr row col E.AliasTakesNoAttribute

-- TYPE ALIASES

chompAliasNameToEquals :: Parser E.TypeAlias (A.Located Name.Name, [A.Located Name.Name])
chompAliasNameToEquals =
  do
    name <- addLocation (Var.upper E.AliasName)
    Space.chompAndCheckIndent E.AliasSpace E.AliasIndentEquals
    chompAliasNameToEqualsHelp name []

chompAliasNameToEqualsHelp :: A.Located Name.Name -> [A.Located Name.Name] -> Parser E.TypeAlias (A.Located Name.Name, [A.Located Name.Name])
chompAliasNameToEqualsHelp name args =
  oneOf
    E.AliasEquals
    [ do
        arg <- addLocation (Var.lower E.AliasEquals)
        Space.chompAndCheckIndent E.AliasSpace E.AliasIndentEquals
        chompAliasNameToEqualsHelp name (arg : args),
      do
        word1 0x3D {-=-} E.AliasEquals
        Space.chompAndCheckIndent E.AliasSpace E.AliasIndentBody
        return (name, reverse args)
    ]

-- CUSTOM TYPES

chompCustomNameToEquals :: Parser E.CustomType (A.Located Name.Name, [([Src.Comment], A.Located Name.Name)], [Src.Comment], [Src.Comment])
chompCustomNameToEquals =
  do
    name <- addLocation (Var.upper E.CT_Name)
    commentsAfterName <- Space.chompAndCheckIndent E.CT_Space E.CT_IndentEquals
    chompCustomNameToEqualsHelp name commentsAfterName []

chompCustomNameToEqualsHelp :: A.Located Name.Name -> [Src.Comment] -> [([Src.Comment], A.Located Name.Name)] -> Parser E.CustomType (A.Located Name.Name, [([Src.Comment], A.Located Name.Name)], [Src.Comment], [Src.Comment])
chompCustomNameToEqualsHelp name commentsAfterPrev args =
  oneOf
    E.CT_Equals
    [ do
        arg <- addLocation (Var.lower E.CT_Equals)
        commentsAfterArg <- Space.chompAndCheckIndent E.CT_Space E.CT_IndentEquals
        chompCustomNameToEqualsHelp name commentsAfterArg ((commentsAfterPrev, arg) : args),
      do
        word1 0x3D {-=-} E.CT_Equals
        commentsAfter <- Space.chompAndCheckIndent E.CT_Space E.CT_IndentAfterEquals
        return (name, reverse args, commentsAfterPrev, commentsAfter)
    ]

chompVariants :: NonEmpty (Src.UnionVariant) -> A.Position -> Space.Parser E.CustomType ([Src.UnionVariant], [Src.Comment])
chompVariants variants@((lastCommentsBefore, lastName, lastArgs, lastCommentsAfter) :| rest) end =
  oneOfWithFallback
    [ do
        Space.checkIndent end E.CT_IndentBar
        word1 0x7C E.CT_Bar
        commentsAfterBar <- Space.chompAndCheckIndent E.CT_Space E.CT_IndentAfterBar
        ((name, args, commentsAfter), newEnd) <- Type.variant
        let variant = (commentsAfterBar, name, args, commentsAfter)
        chompVariants (NonEmpty.cons variant variants) newEnd
    ]
    ( let (commentsAfterLastVariant, commentsAfter) = List.span (A.isIndentedMoreThan 1) lastCommentsAfter
       in ((reverse ((lastCommentsBefore, lastName, lastArgs, commentsAfterLastVariant) : rest), commentsAfter), end)
    )

-- PORT

portDecl :: Maybe Src.DocComment -> Space.Parser E.Decl (Decl, [Src.Comment])
portDecl maybeDocs =
  inContext E.Port (Keyword.port_ E.DeclStart) $
    do
      Space.chompAndCheckIndent E.PortSpace E.PortIndentName
      name <- addLocation (Var.lower E.PortName)
      Space.chompAndCheckIndent E.PortSpace E.PortIndentColon
      word1 0x3A {-:-} E.PortColon
      Space.chompAndCheckIndent E.PortSpace E.PortIndentType
      ((tipe, commentsAfterTipe), end) <- specialize E.PortType Type.expression
      return
        ( (Port maybeDocs (Src.Port name tipe), commentsAfterTipe),
          end
        )

-- INFIX

-- INVARIANT: always chomps to a freshline
--
infix_ :: Parser E.Module (A.Located Src.Infix, [Src.Comment])
infix_ =
  let err = E.Infix
      _err = \_ -> E.Infix
   in do
        start <- getPosition
        Keyword.infix_ err
        Space.chompAndCheckIndent _err err
        associativity <-
          oneOf
            err
            [ Keyword.left_ err >> return Binop.Left,
              Keyword.right_ err >> return Binop.Right,
              Keyword.non_ err >> return Binop.Non
            ]
        Space.chompAndCheckIndent _err err
        precedence <- Number.precedence err
        Space.chompAndCheckIndent _err err
        word1 0x28 {-(-} err
        op <- Symbol.operator err _err
        word1 0x29 {-)-} err
        Space.chompAndCheckIndent _err err
        word1 0x3D {-=-} err
        Space.chompAndCheckIndent _err err
        name <- Var.lower err
        end <- getPosition
        commentsAfter <- Space.chomp _err
        Space.checkFreshLine err
        return (A.at start end (Src.Infix op associativity precedence name), commentsAfter)
