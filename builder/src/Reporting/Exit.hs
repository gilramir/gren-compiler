{-# LANGUAGE OverloadedStrings #-}

module Reporting.Exit
  ( Diff (..),
    diffToReport,
    Make (..),
    makeToReport,
    Docs (..),
    docsToReport,
    Bump (..),
    bumpToReport,
    Repl (..),
    replToReport,
    Validate (..),
    validateToReport,
    newPackageOverview,
    --
    OutlineProblem (..),
    PossibleFilePath (..),
    Details (..),
    DetailsBadDep (..),
    TargetDrift (..),
    BuildProblem (..),
    BuildProjectProblem (..),
    DocsProblem (..),
    Generate (..),
    --
    toString,
    toStderr,
    toJson,
  )
where

import Core.AST qualified as Core
import Core.Target qualified as Target
import Data.ByteString qualified as BS
import Data.ByteString.UTF8 qualified as BS_UTF8
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Name qualified as N
import Data.NonEmptyList qualified as NE
import Data.Set qualified as Set
import Gren.Constraint qualified as C
import Gren.Magnitude qualified as M
import Gren.ModuleName qualified as ModuleName
import Gren.Package qualified as Pkg
import Gren.Version qualified as V
import Json.Encode qualified as Encode
import Json.String qualified as Json
import Parse.Primitives (Col, Row)
import Reporting.Doc qualified as D
import Reporting.Error qualified as Error
import Reporting.Error.Import qualified as Import
import Reporting.Exit.Help qualified as Help
import System.FilePath ((<.>), (</>))
import System.FilePath qualified as FP

-- RENDERERS

toString :: Help.Report -> String
toString report =
  Help.toString (Help.reportToDoc report)

toStderr :: Help.Report -> IO ()
toStderr report =
  Help.toStderr (Help.reportToDoc report)

toJson :: Help.Report -> Encode.Value
toJson report =
  Help.reportToJson report

-- DIFF

data Diff
  = DiffNoOutline
  | DiffApplication
  | DiffNoExposed
  | DiffUnpublished
  | DiffUnknownPackage Pkg.Name [Pkg.Name]
  | DiffUnknownVersion Pkg.Name V.Version [V.Version]
  | DiffDocsProblem V.Version DocsProblem
  | DiffBadDetails Details
  | DiffBadBuild BuildProblem

diffToReport :: Diff -> Help.Report
diffToReport diff =
  case diff of
    DiffNoOutline ->
      Help.report
        "DIFF WHAT?"
        Nothing
        "I cannot find a geng.toml so I am not sure what you want me to diff.\
        \ Normally you run `geng diff` from within a project!"
        [ D.reflow $ "If you are just curious to see a diff, try running this command:",
          D.indent 4 $ D.green $ "geng diff gren/http 1.0.0 2.0.0"
        ]
    DiffApplication ->
      Help.report
        "CANNOT DIFF APPLICATIONS"
        (Just "geng.toml")
        "Your geng.toml says this project is an application, but `geng diff` only works\
        \ with packages."
        [ D.reflow $ "If you are just curious to see a diff, try running this command:",
          D.indent 4 $ D.dullyellow $ "geng diff gren/json 1.0.0 1.1.2"
        ]
    DiffNoExposed ->
      Help.report
        "NO EXPOSED MODULES"
        (Just "geng.toml")
        "Your geng.toml exposes no modules, which means there is no public API at\
        \ all right now! What am I supposed to diff?"
        [ D.reflow $
            "Try adding some modules back to `exposed` in the [modules] table."
        ]
    DiffUnpublished ->
      Help.report
        "UNTAGGED"
        Nothing
        "This package has no semver formatted tags. There is nothing to diff against!"
        []
    DiffUnknownPackage pkg suggestions ->
      Help.report
        "UNKNOWN PACKAGE"
        Nothing
        ("I cannot find a package called:")
        [ D.indent 4 $ D.red $ D.fromChars $ Pkg.toChars pkg,
          "Maybe you want one of these instead?",
          D.indent 4 $ D.dullyellow $ D.vcat $ map (D.fromChars . Pkg.toChars) suggestions,
          "But check <https://packages.gren-lang.org> to see all possibilities!"
        ]
    DiffUnknownVersion _pkg vsn realVersions ->
      Help.docReport
        "UNKNOWN VERSION"
        Nothing
        ( D.fillSep $
            [ "Found",
              "no",
              D.red (D.fromVersion vsn),
              "tag",
              "so",
              "I",
              "cannot",
              "diff",
              "against",
              "it."
            ]
        )
        [ "Here are all the semver formatted tags I did find:",
          D.indent 4 $
            D.dullyellow $
              D.vcat $
                let sameMajor v1 v2 = V._major v1 == V._major v2
                    mkRow vsns = D.hsep $ map D.fromVersion vsns
                 in map mkRow $ List.groupBy sameMajor (List.sort realVersions),
          "Want one of those instead?"
        ]
    DiffDocsProblem version problem ->
      toDocsProblemReport problem $
        "I need the docs for " ++ V.toChars version ++ " to compute this diff"
    DiffBadDetails details ->
      toDetailsReport details
    DiffBadBuild buildProblem ->
      toBuildProblemReport buildProblem

-- BUMP

data Bump
  = BumpNoOutline
  | BumpApplication
  | BumpUnexpectedVersion V.Version [V.Version]
  | BumpBadDetails Details
  | BumpNoExposed
  | BumpBadBuild BuildProblem
  | BumpCannotFindDocs Pkg.Name V.Version DocsProblem

bumpToReport :: Bump -> Help.Report
bumpToReport bump =
  case bump of
    BumpNoOutline ->
      Help.report
        "BUMP WHAT?"
        Nothing
        "I cannot find a geng.toml so I am not sure what you want me to bump."
        [ D.reflow $
            "Geng packages always have a geng.toml that says the current version number. If\
            \ you run this command from a directory with a geng.toml file, I will try to bump\
            \ the version in there based on the API changes."
        ]
    BumpApplication ->
      Help.report
        "CANNOT BUMP APPLICATIONS"
        (Just "geng.toml")
        "Your geng.toml says this is an application. That means it cannot be used\
        \ installed as a dependency in another project. There's no need to handle\
        \ versioning of applications."
        []
    BumpUnexpectedVersion vsn versions ->
      Help.docReport
        "CANNOT BUMP"
        (Just "geng.toml")
        ( D.fillSep
            [ "Your",
              "geng.toml",
              "says",
              "I",
              "should",
              "bump",
              "relative",
              "to",
              "version",
              D.red (D.fromVersion vsn) <> ",",
              "but",
              "I",
              "cannot",
              "find",
              "that",
              "version",
              "on",
              "<https://packages.gren-lang.org>.",
              "That",
              "means",
              "there",
              "is",
              "no",
              "API",
              "for",
              "me",
              "to",
              "diff",
              "against",
              "and",
              "figure",
              "out",
              "if",
              "these",
              "are",
              "MAJOR,",
              "MINOR,",
              "or",
              "PATCH",
              "changes."
            ]
        )
        [ D.fillSep $
            ["Try", "bumping", "again", "after", "changing", "the", D.dullyellow "version", "in", "geng.toml"]
              ++ if length versions == 1 then ["to:"] else ["to", "one", "of", "these:"],
          D.vcat $ map (D.green . D.fromVersion) versions
        ]
    BumpBadDetails details ->
      toDetailsReport details
    BumpNoExposed ->
      Help.docReport
        "NO EXPOSED MODULES"
        (Just "geng.toml")
        ( D.fillSep
            [ "To",
              "bump",
              "a",
              "package,",
              "the",
              D.dullyellow "[modules]",
              "table",
              "of",
              "your",
              "geng.toml",
              "must",
              "list",
              "at",
              "least",
              "one",
              "module."
            ]
        )
        [ D.reflow
            "Try adding some modules back to `exposed` in the [modules] table."
        ]
    BumpBadBuild problem ->
      toBuildProblemReport problem
    BumpCannotFindDocs _ vsn problem ->
      toDocsProblemReport problem $
        "I need the docs for " ++ V.toChars vsn ++ " to compute the next version number"

-- DOCS

data Docs
  = DocsNoOutline
  | DocsApplication
  | DocsBadDetails Details
  | DocsNoExposed
  | DocsBadBuild BuildProblem

docsToReport :: Docs -> Help.Report
docsToReport docs =
  case docs of
    DocsNoOutline ->
      Help.report
        "BUILD DOCS FOR WHAT?"
        Nothing
        "I cannot find a geng.toml file so I am not sure what you want me to generate docs for."
        [ D.reflow
            "Geng packages always have a geng.toml file that defines a project. If\
            \ you run this command from a directory with a geng.toml file, I will try to generate\
            \ documentation for the modules its [modules] table exposes."
        ]
    DocsApplication ->
      Help.report
        "CANNOT BUILD DOCS FOR APPLICATIONS"
        (Just "geng.toml")
        "Your geng.toml file says this is an application. Documentation is only generated\
        \ for packages."
        []
    DocsBadDetails details ->
      toDetailsReport details
    DocsNoExposed ->
      Help.docReport
        "NO EXPOSED MODULES"
        (Just "geng.toml")
        ( D.fillSep
            [ "To",
              "build",
              "documentation",
              "for",
              "a",
              "package,",
              "the",
              D.dullyellow "[modules]",
              "table",
              "of",
              "your",
              "geng.toml",
              "must",
              "list",
              "at",
              "least",
              "one",
              "module."
            ]
        )
        [ D.reflow
            "Try adding some modules back to `exposed` in the [modules] table."
        ]
    DocsBadBuild problem ->
      toBuildProblemReport problem

-- OVERVIEW OF VERSIONING

newPackageOverview :: String
newPackageOverview =
  unlines
    [ "This package hasn't been tagged with a semver version. Here's how things work:",
      "",
      "  - Versions all have exactly three parts: MAJOR.MINOR.PATCH",
      "",
      "  - All packages start with initial version " ++ V.toChars V.one,
      "",
      "  - Versions are incremented based on how the API changes:",
      "",
      "        PATCH = the API is the same, no risk of breaking code",
      "        MINOR = values have been added, existing values are unchanged",
      "        MAJOR = existing values have been changed or removed",
      "",
      "  - I will bump versions for you, automatically enforcing these rules",
      ""
    ]

-- VALIDATE

data Validate
  = ValidateNoOutline
  | ValidateBadDetails Details
  | ValidateApplication
  | ValidateNotInitialVersion V.Version
  | ValidateInvalidBump V.Version V.Version
  | ValidateBadBump V.Version V.Version M.Magnitude V.Version M.Magnitude
  | ValidateNoSummary
  | ValidateNoExposed
  | ValidateNoReadme
  | ValidateShortReadme
  | ValidateNoLicense
  | ValidateBuildProblem BuildProblem
  | ValidateCannotGetDocs V.Version V.Version DocsProblem
  | ValidateMissingTag V.Version
  | ValidateNoGit
  | ValidateLocalChanges V.Version

validateToReport :: Validate -> Help.Report
validateToReport validate =
  case validate of
    ValidateNoOutline ->
      Help.report
        "VALIDATE WHAT?"
        Nothing
        "I cannot find a geng.toml so I am not sure what you want me to validate."
        [ D.reflow $
            "Geng packages always have a geng.toml that states the version number,\
            \ dependencies, exposed modules, etc."
        ]
    ValidateBadDetails problem ->
      toDetailsReport problem
    ValidateApplication ->
      Help.report
        "NOT A PACKAGE"
        Nothing
        "I cannot validate applications, only packages!"
        []
    ValidateNotInitialVersion vsn ->
      Help.docReport
        "INVALID VERSION"
        Nothing
        ( D.fillSep
            [ "I",
              "cannot",
              "validate",
              D.red (D.fromVersion vsn),
              "as",
              "the",
              "initial",
              "version."
            ]
        )
        [ D.fillSep
            [ "Change",
              "it",
              "to",
              D.green "1.0.0",
              "which",
              "is",
              "the",
              "initial",
              "version",
              "for",
              "all",
              "Gren",
              "packages."
            ]
        ]
    ValidateInvalidBump statedVersion latestVersion ->
      Help.docReport
        "INVALID VERSION"
        (Just "geng.toml")
        ( D.fillSep $
            [ "Your",
              "geng.toml",
              "says",
              "the",
              "next",
              "version",
              "should",
              "be",
              D.red (D.fromVersion statedVersion) <> ",",
              "but",
              "that",
              "is",
              "not",
              "valid",
              "based",
              "on",
              "the",
              "previously",
              "tagged",
              "versions."
            ]
        )
        [ D.fillSep $
            [ "Change",
              "the",
              "version",
              "back",
              "to",
              D.green (D.fromVersion latestVersion),
              "which",
              "is",
              "the",
              "most",
              "recently",
              "tagged",
              "version.",
              "From",
              "there,",
              "have",
              "Gren",
              "bump",
              "the",
              "version",
              "by",
              "running:"
            ],
          D.indent 4 $ D.green "geng bump",
          D.reflow $
            "If you want more insight on the API changes Gren detects, you\
            \ can run `geng diff` at this point as well."
        ]
    ValidateBadBump old new magnitude realNew realMagnitude ->
      Help.docReport
        "INVALID VERSION"
        (Just "geng.toml")
        ( D.fillSep $
            [ "Your",
              "geng.toml",
              "says",
              "the",
              "next",
              "version",
              "should",
              "be",
              D.red (D.fromVersion new) <> ",",
              "indicating",
              "a",
              D.fromChars (M.toChars magnitude),
              "change",
              "to",
              "the",
              "public",
              "API.",
              "This",
              "does",
              "not",
              "match",
              "the",
              "API",
              "diff",
              "given",
              "by:"
            ]
        )
        [ D.indent 4 $
            D.fromChars $
              "geng diff " ++ V.toChars old,
          D.fillSep $
            [ "This",
              "command",
              "says",
              "this",
              "is",
              "a",
              D.fromChars (M.toChars realMagnitude),
              "change,",
              "so",
              "the",
              "next",
              "version",
              "should",
              "be",
              D.green (D.fromVersion realNew) <> "."
            ],
          D.reflow $
            "Also, next time use `geng bump` and I'll figure all this out for you!"
        ]
    ValidateNoSummary ->
      Help.docReport
        "NO SUMMARY"
        (Just "geng.toml")
        ( D.fillSep $
            [ "Every",
              "package,",
              "should",
              "have",
              "a",
              D.dullyellow "\"summary\"",
              "field",
              "in",
              "the",
              "geng.toml",
              "file",
              "that",
              "gives",
              "a",
              "consice",
              "overview",
              "of",
              "the",
              "project."
            ]
        )
        [ D.reflow $
            "The summary must be less than 80 characters. It should describe\
            \ the concrete use of your package as clearly and as plainly as possible."
        ]
    ValidateNoExposed ->
      Help.docReport
        "NO EXPOSED MODULES"
        (Just "geng.toml")
        ( D.fillSep $
            [ "The",
              D.dullyellow "[modules]",
              "table",
              "of",
              "your",
              "geng.toml",
              "must",
              "list",
              "at",
              "least",
              "one",
              "module."
            ]
        )
        [ D.reflow $
            "Which modules do you want users of the package to have access to? Add their\
            \ names to `exposed` in the [modules] table."
        ]
    ValidateNoReadme ->
      toBadReadmeReport "NO README" $
        "Every package should have a helpful README.md\
        \ file, but I do not see one in your project."
    ValidateShortReadme ->
      toBadReadmeReport "SHORT README" $
        "This README.md is too short. Having more details will help\
        \ people assess your package quickly and fairly."
    ValidateNoLicense ->
      Help.report
        "NO LICENSE FILE"
        (Just "LICENSE")
        "By making a package available you are inviting the Gren community to build\
        \ upon your work. But without knowing your license, we have no idea if\
        \ that is legal!"
        [ D.reflow $
            "Once you pick an OSI approved license from <https://spdx.org/licenses/>,\
            \ you must share that choice in two places. First, the license\
            \ identifier must appear in your geng.toml file. Second, the full\
            \ license text must appear in the root of your project in a file\
            \ named LICENSE. Add that file and you will be all set!"
        ]
    ValidateBuildProblem buildProblem ->
      toBuildProblemReport buildProblem
    ValidateCannotGetDocs old new docsProblem ->
      toDocsProblemReport docsProblem $
        "I need the docs for "
          ++ V.toChars old
          ++ " to verify that "
          ++ V.toChars new
          ++ " really does come next"
    ValidateMissingTag version ->
      let vsn = V.toChars version
       in Help.docReport
            "NO TAG"
            Nothing
            ( D.fillSep $
                [ "Packages",
                  "must",
                  "be",
                  "tagged",
                  "in",
                  "git,",
                  "but",
                  "I",
                  "cannot",
                  "find",
                  "a",
                  D.green (D.fromChars vsn),
                  "tag."
                ]
            )
            [ D.vcat
                [ "These tags make it possible to find this specific version on GitHub.",
                  "To tag the most recent commit and push it to GitHub, run this:"
                ],
              D.indent 4 $
                D.dullyellow $
                  D.vcat $
                    map D.fromChars $
                      [ "git tag -a " ++ vsn ++ " -m \"new release\"",
                        "git push origin " ++ vsn
                      ],
              "The -m flag is for a helpful message. Try to make it more informative!"
            ]
    ValidateNoGit ->
      Help.report
        "NO GIT"
        Nothing
        "I searched your PATH environment variable for `git` and could not\
        \ find it. Is it available through your PATH?"
        [ D.reflow $
            "Who cares about this? Well, I currently use `git` to check if there\
            \ are any local changes in your code. Local changes are a good sign\
            \ that some important improvements have gotten mistagged, so this\
            \ check can be extremely helpful for package authors!",
          D.toSimpleNote $
            "We plan to do this without the `git` binary in a future release."
        ]
    ValidateLocalChanges version ->
      let vsn = V.toChars version
       in Help.docReport
            "LOCAL CHANGES"
            Nothing
            ( D.fillSep $
                [ "The",
                  "code",
                  "tagged",
                  "as",
                  D.green (D.fromChars vsn),
                  "in",
                  "git",
                  "does",
                  "not",
                  "match",
                  "the",
                  "code",
                  "in",
                  "your",
                  "working",
                  "directory.",
                  "This",
                  "means",
                  "you",
                  "have",
                  "commits",
                  "or",
                  "local",
                  "changes",
                  "that",
                  "are",
                  "not",
                  "going",
                  "to",
                  "be",
                  "available",
                  "when",
                  "downloaded!"
                ]
            )
            []

toBadReadmeReport :: String -> String -> Help.Report
toBadReadmeReport title summary =
  Help.report
    title
    (Just "README.md")
    summary
    [ D.reflow $
        "When people look at your README, they are wondering:",
      D.vcat
        [ "  - What does this package even do?",
          "  - Will it help me solve MY problems?"
        ],
      D.reflow $
        "So I recommend starting your README with a small example of the\
        \ most common usage scenario. Show people what they can expect if\
        \ they learn more!",
      D.toSimpleNote $
        "By tagging your package, you are inviting people to invest time in\
        \ understanding your work. Spending an hour on your README to communicate your\
        \ knowledge more clearly can save the community days or weeks of time in\
        \ aggregate, and saving time in aggregate is the whole point of building\
        \ packages! People really appreciate it, and it makes the whole ecosystem feel\
        \ nicer!"
    ]

-- DOCS

data DocsProblem
  = DP_Git ()
  | DP_Data String BS.ByteString
  | DP_Cache

toDocsProblemReport :: DocsProblem -> String -> Help.Report
toDocsProblemReport problem context =
  case problem of
    DP_Git gitError ->
      toGitErrorReport "PROBLEM LOADING DOCS" gitError context
    DP_Data url body ->
      Help.report
        "PROBLEM LOADING DOCS"
        Nothing
        (context ++ ", so I fetched:")
        [ D.indent 4 $ D.dullyellow $ D.fromChars url,
          D.reflow $
            "I got the data back, but it was not what I was expecting. The response\
            \ body contains "
              ++ show (BS.length body)
              ++ " bytes. Here is the "
              ++ if BS.length body <= 76 then "whole thing:" else "beginning:",
          D.indent 4 $
            D.dullyellow $
              D.fromChars $
                if BS.length body <= 76
                  then BS_UTF8.toString body
                  else take 73 (BS_UTF8.toString body) ++ "...",
          D.reflow
            "Does this error keep showing up? Maybe there is something weird with your\
            \ internet connection."
        ]
    DP_Cache ->
      Help.report
        "PROBLEM LOADING DOCS"
        Nothing
        (context ++ ", but the local copy seems to be corrupted.")
        [ D.reflow
            "I deleted the cached version, so the next run should download a fresh copy of\
            \ the docs. Hopefully that will get you unstuck, but it will not resolve the root\
            \ problem if, for example, a 3rd party editor plugin is modifing cached files\
            \ for some reason."
        ]

-- OUTLINE

data OutlineProblem
  = OP_BadType
  | OP_BadPkgName Row Col
  | OP_BadVersion (PossibleFilePath (Row, Col))
  | OP_BadConstraint (PossibleFilePath C.Error)
  | OP_BadModuleName Row Col
  | OP_BadModuleHeaderTooLong
  | OP_BadDependencyName Row Col
  | OP_BadLicense Json.String [Json.String]
  | OP_BadSummaryTooLong
  | OP_NoSrcDirs
  | OP_BadPlatform
  | OP_BadTarget

data PossibleFilePath otherError
  = OP_AttemptedFilePath (Row, Col)
  | OP_AttemptedOther otherError

-- DETAILS

data Details
  = DetailsBadDeps FilePath [DetailsBadDep]

data DetailsBadDep
  = BD_BadBuild Pkg.Name V.Version (Map.Map Pkg.Name V.Version)
  | BD_UnsignedBuild Pkg.Name V.Version
  | BD_TargetDrift TargetDrift

-- | A package whose declared @target@ is not what its externs serve (D50,
-- D318): the package, what it declares, what is derived, and for each target
-- it declares and does not serve, the modules that are why.
data TargetDrift = TargetDrift Pkg.Name (Set.Set Target.Target) (Set.Set Target.Target) [(Target.Target, [Target.Refusal])]

toDetailsReport :: Details -> Help.Report
toDetailsReport details =
  case details of
    DetailsBadDeps cacheDir deps ->
      case deps of
        [] ->
          Help.report
            "PROBLEM BUILDING DEPENDENCIES"
            Nothing
            "I am not sure what is going wrong though."
            [ D.reflow $
                "I would try deleting the "
                  ++ cacheDir
                  ++ " and .gren/ directories, then\
                     \ trying to build again. That will work if some cached files got corrupted\
                     \ somehow.",
              D.reflow $
                "If that does not work, go to https://gren-lang.org/community and ask for\
                \ help. This is a weird case!"
            ]
        d : _ ->
          case d of
            BD_BadBuild pkg vsn fingerprint ->
              Help.report
                "PROBLEM BUILDING DEPENDENCIES"
                Nothing
                "I ran into a compilation error when trying to build the following package:"
                [ D.indent 4 $ D.red $ D.fromChars $ Pkg.toChars pkg ++ " " ++ V.toChars vsn,
                  D.reflow
                    "This probably means it has package constraints that are too wide. It may be\
                    \ possible to tweak your geng.toml to avoid the root problem as a stopgap. Head\
                    \ over to https://gren-lang.org/community to get help figuring out how to take\
                    \ this path!",
                  D.toSimpleNote
                    "To help with the root problem, please report this to the package author along\
                    \ with the following information:",
                  D.indent 4 $
                    D.vcat $
                      map (\(p, v) -> D.fromChars $ Pkg.toChars p ++ " " ++ V.toChars v) $
                        Map.toList fingerprint,
                  D.reflow
                    "If you want to help out even more, try building the package locally. That should\
                    \ give you much more specific information about why this package is failing to\
                    \ build, which will in turn make it easier for the package author to fix it!"
                ]
            BD_TargetDrift drift ->
              targetDriftReport drift
            BD_UnsignedBuild pkg vsn ->
              Help.report
                "PROBLEM BUILDING DEPENDENCIES (UNSIGNED KERNEL CODE)"
                Nothing
                "I ran into a compilation error when trying to build the following package:"
                [ D.indent 4 $ D.red $ D.fromChars $ Pkg.toChars pkg ++ " " ++ V.toChars vsn,
                  D.reflow
                    "This package contains kernel code which has not been signed by Gren's core\
                    \ team. Kernel code can violate all the guarantees that Gren\
                    \ provide, and is therefore carefully managed.",
                  D.toSimpleNote $
                    "To help with the root problem, please report this to the package author."
                ]

-- TARGETS

targetDriftReport :: TargetDrift -> Help.Report
targetDriftReport (TargetDrift pkg declared derived refused) =
  Help.report
    "TARGET DOES NOT MATCH THE EXTERNS"
    Nothing
    ( "The geng.toml of "
        ++ Pkg.toChars pkg
        ++ " says its target is "
        ++ targetsToChars declared
        ++ ", and its externs serve "
        ++ targetsToChars derived
        ++ "."
    )
    ( [ D.indent 4 $
          D.vcat $
            concat
              [ D.fromChars (Target.toChars target ++ " is not served by:") : map (D.indent 4 . refusalDoc) refusals
              | (target, refusals) <- refused
              ]
      | not (null refused)
      ]
        ++ [ D.reflow $
               "The target is derived from the externs, so writing it down only has it checked. Write\
               \ target = "
                 ++ targetsToToml derived
                 ++ ", or leave it out (packaging.md K3, D50, D318)."
           ]
    )

-- | A set of targets as a sentence says it.
targetsToChars :: Set.Set Target.Target -> String
targetsToChars targets
  | targets == Target.everything = "any"
  | Set.null targets = "no target"
  | otherwise =
      case map Target.toChars (Set.toAscList targets) of
        [one] -> one
        names -> List.intercalate ", " (init names) ++ " and " ++ last names

-- | A set of targets as @geng.toml@ writes it.
targetsToToml :: Set.Set Target.Target -> String
targetsToToml targets
  | targets == Target.everything = "\"any\""
  | otherwise = "[" ++ List.intercalate ", " (map (show . Target.toChars) (Set.toAscList targets)) ++ "]"

-- | The modules that refuse a target, under their packages.
refusalDocs :: [Target.Refusal] -> [D.Doc]
refusalDocs refusals =
  concat
    [ D.fromChars (packageToChars pkg) : map (D.indent 4 . refusalDoc) group
    | group@(first : _) <- List.groupBy (\a b -> packageOf a == packageOf b) (List.sortOn sortKey refusals),
      let pkg = packageOf first
    ]
  where
    packageOf = ModuleName._package . Target._refusalModule
    sortKey (Target.Refusal (ModuleName.Canonical pkg name) _) = (Pkg.toChars pkg, ModuleName.toChars name)
    packageToChars pkg =
      if pkg == Pkg.application then "the application" else Pkg.toChars pkg

-- | One module that refuses a target: its declarations, each with the languages
-- it has rows for.
refusalDoc :: Target.Refusal -> D.Doc
refusalDoc (Target.Refusal home externs) =
  D.fromChars $
    ModuleName.toChars (ModuleName._module home)
      ++ ": "
      ++ List.intercalate ", " [N.toChars name ++ " (" ++ List.intercalate ", " (map languageToChars languages) ++ ")" | (name, languages) <- externs]
  where
    languageToChars language =
      case language of
        Core.ExternJs -> "js"
        Core.ExternErlang -> "erlang"
        Core.ExternC -> "c"

--

toGitErrorReport :: String -> () -> String -> Help.Report
toGitErrorReport title _ _ =
  Help.report title Nothing "" []

--   let toGitReport intro details =
--         Help.report title Nothing intro details
--    in case err of
--         Git.MissingGit ->
--           toGitReport
--             (context ++ ", but I couldn't find a git binary.")
--             [ D.reflow
--                 "I use git to clone dependencies from github.\
--                 \ Make sure that git is installed and present in your PATH."
--             ]
--         Git.NoVersions ->
--           toGitReport
--             (context ++ ", but I couldn't find any semver compatible tags in this repo.")
--             [ D.reflow
--                 "Gren packages are just git repositories with tags following the \
--                 \ semantic versioning scheme. However, it seems that this particular repo \
--                 \ doesn't have _any_ semantic version tags!"
--             ]
--         Git.NoSuchRepo ->
--           toGitReport
--             (context ++ ", but I couldn't find the repo on github.")
--             [ D.reflow
--                 "Gren packages are just git repositories hosted on github, however \
--                 \ it seems like this repo doesn't exist."
--             ]
--         Git.NoSuchRepoOrVersion vsn ->
--           toGitReport
--             (context ++ ", but I couldn't find the correct version of this package on github.")
--             [ D.reflow $
--                 "Gren packages are just git repositories hosted on github with semver \
--                 \ formatted tags. However, it seems like this package, or version "
--                   ++ V.toChars vsn
--                   ++ ", doesn't exist."
--             ]
--         Git.FailedCommand args errorMsg ->
--           toGitReport
--             (context ++ ", so I tried to execute:")
--             [ D.indent 4 $ D.reflow $ unwords args,
--               D.reflow "But it returned the following error message:",
--               D.indent 4 $ D.reflow errorMsg
--             ]

-- MAKE

data Make
  = MakeNoOutline
  | MakeCannotOutputForPackage
  | MakeCannotOutputMainForPackage ModuleName.Raw [ModuleName.Raw]
  | MakeBadDetails Details
  | MakeAppNeedsFileNames
  | MakePkgNeedsExposing
  | MakeMultipleFiles
  | MakeNoMain
  | MakeNonMainFilesIntoJavaScript ModuleName.Raw [ModuleName.Raw]
  | MakeCannotBuild BuildProblem
  | MakeBadGenerate Generate
  | MakeHtmlOnlyForBrowserPlatform
  | MakeExeOnlyForNodePlatform
  | MakeBeamManyMains ModuleName.Raw ModuleName.Raw [ModuleName.Raw]
  | MakeBeamNothingToCall ModuleName.Raw [ModuleName.Raw]

makeToReport :: Make -> Help.Report
makeToReport make =
  case make of
    MakeNoOutline ->
      Help.report
        "NO geng.toml FILE"
        Nothing
        "It looks like you are starting a new Gren project. Very exciting! Try running:"
        [ D.indent 4 $ D.green $ "geng init",
          D.reflow $
            "It will help you get set up. It is really simple!"
        ]
    MakeCannotOutputForPackage ->
      Help.docReport
        "IMPOSSIBLE TO PRODUCE OUTPUT FOR A PACKAGE"
        Nothing
        ( D.fillSep
            [ "I",
              "cannot",
              "produce",
              "output",
              "requested",
              "by",
              "the",
              D.dullyellow "--output",
              "flag",
              "for",
              "a",
              "project",
              "of",
              "type",
              D.dullyellow "package."
            ]
        )
        [ D.reflow $
            "If you only wanted to verify that your package builds correctly, try to remove the `--output` flag\
            \ from your `geng make` command.",
          D.reflow $
            "Your project is a `[package]` in your `geng.toml`. This means that your project\
            \ is meant to be used as a Gren package and cannot be compiled to any kind of output. Instead, it's \
            \ meant to be consumed in its source form by another package or application. If you want to test your \
            \ package with an application, simply create a separate project of type `application` and include this \
            \ project in the `source-directories` of the application's `geng.toml`."
        ]
    MakeCannotOutputMainForPackage m ms ->
      Help.report
        "IMPOSSIBLE TO PRODUCE OUTPUT FOR MAIN IN A PACKAGE"
        Nothing
        "I cannot produce output by compiling the given modules:"
        [ D.indent 4 $ D.red $ D.vcat $ map D.fromName (m : ms),
          D.fillSep
            [ "They",
              "contain",
              "definitions",
              "for",
              D.dullyellow "main",
              "functions,",
              "which",
              "would",
              "normally",
              "produce",
              "html",
              "output",
              "but",
              "your",
              "project",
              "is",
              "of",
              "type",
              D.dullyellow "package."
            ],
          D.reflow $
            "If you only wanted to verify that your package builds correctly, try to remove the output paths to\
            \ these modules from your `geng make` command or remove the main functions from the mentioned modules.",
          D.reflow $
            "Your project is a `[package]` in your `geng.toml`. This means that your project\
            \ is meant to be used as a Gren package and cannot be compiled to any kind of output. Instead, it's \
            \ meant to be consumed in its source form by another package or application. If you want to test your\
            \ package with an application, simply create a separate project of type `application` and include this\
            \ project in the `source-directories` of the application's `geng.toml`."
        ]
    MakeBadDetails detailsProblem ->
      toDetailsReport detailsProblem
    MakeAppNeedsFileNames ->
      Help.report
        "NO INPUT"
        Nothing
        "What should I make though? I need specific files like:"
        [ D.vcat
            [ D.indent 4 $ D.green "geng make Main",
              D.indent 4 $ D.green "geng make This That"
            ],
          D.reflow $
            "I recommend reading through https://gren-lang.org/learn for guidance on what to\
            \ actually put in those files!"
        ]
    MakePkgNeedsExposing ->
      Help.report
        "NO INPUT"
        Nothing
        "What should I make though? I need specific files like:"
        [ D.vcat
            [ D.indent 4 $ D.green "geng make Main",
              D.indent 4 $ D.green "geng make This That"
            ],
          D.reflow $
            "You can also add modules to `exposed` in the [modules] table of your geng.toml, and\
            \ I will try to compile the relevant files."
        ]
    MakeBeamManyMains m1 m2 ms ->
      Help.report
        "TOO MANY MAINS"
        Nothing
        "A BEAM program has one entry point, and these modules each have a `main`:"
        [ D.indent 4 $ D.red $ D.vcat $ map D.fromName (m1 : m2 : ms),
          D.reflow
            "Name one of them, and the others' exposed values can be built beside it: a\
            \ module with no `main` is a library, whose exposed values are exported for Erlang\
            \ to call (m2-interop.md D399)."
        ]
    MakeBeamNothingToCall m ms ->
      Help.report
        "NOTHING TO BUILD"
        Nothing
        "A build for the beam target starts from the modules it is given: a `main`, and\
        \ every value they expose, which is what Erlang may call. These have neither:"
        [ D.indent 4 $ D.red $ D.vcat $ map D.fromName (m : ms),
          D.reflow
            "Add the values Erlang is to call to the module's `exposing`, or a `main`, or\
            \ switch to --output=/dev/null to check that it compiles without building\
            \ anything (m2-interop.md D399)."
        ]
    MakeMultipleFiles ->
      Help.report
        "TOO MANY FILES"
        Nothing
        ("When producing an HTML file or executable, I can only handle one file.")
        [ D.fillSep
            [ "Switch",
              "to",
              D.dullyellow "--output=/dev/null",
              "if",
              "you",
              "just",
              "want",
              "to",
              "get",
              "compile",
              "errors.",
              "This",
              "skips",
              "the",
              "code",
              "gen",
              "phase,",
              "so",
              "it",
              "can",
              "be",
              "a",
              "bit",
              "faster",
              "than",
              "other",
              "options",
              "sometimes."
            ],
          D.fillSep
            [ "Switch",
              "to",
              D.dullyellow "--output=gren.js",
              "if",
              "you",
              "want",
              "multiple",
              "`main`",
              "values",
              "available",
              "in",
              "a",
              "single",
              "JavaScript",
              "file.",
              "Then",
              "you",
              "can",
              "make",
              "your",
              "own",
              "customized",
              "HTML",
              "file",
              "that",
              "embeds",
              "multiple",
              "Gren",
              "nodes.",
              "The",
              "generated",
              "JavaScript",
              "also",
              "shares",
              "dependencies",
              "between",
              "modules,",
              "so",
              "it",
              "should",
              "be",
              "smaller",
              "than",
              "compiling",
              "each",
              "module",
              "separately."
            ]
        ]
    MakeNoMain ->
      Help.report
        "NO MAIN"
        Nothing
        ( "When producing an HTML file, I require that the given file has a `main` value.\
          \ That way I have something to show on screen!"
        )
        [ D.reflow $
            "Try adding a `main` value to your file? Or if you just want to verify that this\
            \ module compiles, switch to --output=/dev/null to skip the code gen phase\
            \ altogether.",
          D.toSimpleNote $
            "Adding a `main` value can be as brief as adding something like this:",
          D.vcat
            [ D.fillSep [D.cyan "import", "Console"],
              "",
              D.fillSep [D.green "main", "="],
              D.indent 4 $ D.fillSep [D.cyan "Console" <> ".write", D.dullyellow "\"Hello!\\n\""]
            ],
          D.reflow $
            "A `main` is a `Task Never {}`, and the program ends when it completes."
        ]
    MakeNonMainFilesIntoJavaScript m ms ->
      case ms of
        [] ->
          Help.report
            "NO MAIN"
            Nothing
            ( "When producing a JS file, I require that the given file has a `main` value. That\
              \ way Gren."
                ++ ModuleName.toChars m
                ++ ".init() is definitely defined in the\
                   \ resulting file!"
            )
            [ D.reflow $
                "Try adding a `main` value to your file? Or if you just want to verify that this\
                \ module compiles, switch to --output=/dev/null to skip the code gen phase\
                \ altogether.",
              D.toSimpleNote $
                "Adding a `main` value can be as brief as adding something like this:",
              D.vcat
                [ D.fillSep [D.cyan "import", "Console"],
                  "",
                  D.fillSep [D.green "main", "="],
                  D.indent 4 $ D.fillSep [D.cyan "Console" <> ".write", D.dullyellow "\"Hello!\\n\""]
                ],
              D.reflow $
                "A `main` is a `Task Never {}`, and the program ends when it completes."
            ]
        _ : _ ->
          Help.report
            "NO MAIN"
            Nothing
            ( "When producing a JS file, I require that given files all have `main` values.\
              \ That way functions like Gren."
                ++ ModuleName.toChars m
                ++ ".init() are\
                   \ definitely defined in the resulting file. I am missing `main` values in:"
            )
            [ D.indent 4 $ D.red $ D.vcat $ map D.fromName (m : ms),
              D.reflow $
                "Try adding a `main` value to them? Or if you just want to verify that these\
                \ modules compile, switch to --output=/dev/null to skip the code gen phase\
                \ altogether.",
              D.toSimpleNote $
                "Adding a `main` value can be as brief as adding something like this:",
              D.vcat
                [ D.fillSep [D.cyan "import", "Console"],
                  "",
                  D.fillSep [D.green "main", "="],
                  D.indent 4 $ D.fillSep [D.cyan "Console" <> ".write", D.dullyellow "\"Hello!\\n\""]
                ],
              D.reflow $
                "A `main` is a `Task Never {}`, and the program ends when it completes."
            ]
    MakeCannotBuild buildProblem ->
      toBuildProblemReport buildProblem
    MakeBadGenerate generateProblem ->
      toGenerateReport generateProblem
    MakeHtmlOnlyForBrowserPlatform ->
      Help.report
        "HTML FILES CAN ONLY BE CREATED FOR BROWSER PLATFORM"
        Nothing
        ("When producing a HTML file, I require that the project platform is `browser`.")
        [ D.reflow $
            "Try changing `runtime` in `geng.toml` to `browser`.\
            \ alternatively, pass a filename ending with `.js` to the compiler."
        ]
    MakeExeOnlyForNodePlatform ->
      Help.report
        "EXECUTABLES CAN ONLY BE CREATED FOR NODE PLATFORM"
        Nothing
        ("When producing an executable, I require that the project platform is `node`.")
        [ D.reflow $
            "Try changing `runtime` in `geng.toml` to `node`.\
            \ alternatively, pass a filename ending with `.js` to the compiler."
        ]

-- BUILD PROBLEM

data BuildProblem
  = BuildBadModules FilePath Error.Module [Error.Module]
  | BuildProjectProblem BuildProjectProblem

data BuildProjectProblem
  = BP_PathUnknown FilePath
  | BP_WithBadExtension FilePath
  | BP_WithAmbiguousSrcDir FilePath FilePath FilePath
  | BP_MainPathDuplicate FilePath FilePath
  | BP_RootNameDuplicate ModuleName.Raw FilePath FilePath
  | BP_RootNameInvalid FilePath FilePath [String]
  | BP_CannotLoadDependencies
  | BP_Cycle ModuleName.Raw [ModuleName.Raw]
  | BP_MissingExposed (NE.List (ModuleName.Raw, Import.Problem))
  | BP_TargetDrift TargetDrift

toBuildProblemReport :: BuildProblem -> Help.Report
toBuildProblemReport problem =
  case problem of
    BuildBadModules root e es ->
      Help.compilerReport root e es
    BuildProjectProblem projectProblem ->
      toProjectProblemReport projectProblem

toProjectProblemReport :: BuildProjectProblem -> Help.Report
toProjectProblemReport projectProblem =
  case projectProblem of
    BP_TargetDrift drift ->
      targetDriftReport drift
    BP_PathUnknown path ->
      Help.report
        "FILE NOT FOUND"
        Nothing
        "I cannot find this file:"
        [ D.indent 4 $ D.red $ D.fromChars path,
          D.reflow $ "Is there a typo?",
          D.toSimpleNote $
            "If you are just getting started, try working through the examples in the\
            \ official guide https://gren-lang.org/learn to get an idea of the kinds of things\
            \ that typically go in a src/Main.geng file."
        ]
    BP_WithBadExtension path ->
      Help.report
        "UNEXPECTED FILE EXTENSION"
        Nothing
        "I can only compile Geng files (with a .geng extension) but you want me to compile:"
        [ D.indent 4 $ D.red $ D.fromChars path,
          D.reflow $ "Is there a typo? Can the file extension be changed?"
        ]
    BP_WithAmbiguousSrcDir path srcDir1 srcDir2 ->
      Help.report
        "CONFUSING FILE"
        Nothing
        "I am getting confused when I try to compile this file:"
        [ D.indent 4 $ D.red $ D.fromChars path,
          D.reflow $
            "I always check if files appear in any of the `source-directories` listed in\
            \ your geng.toml to see if there might be some cached information about them. That\
            \ can help me compile faster! But in this case, it looks like this file may be in\
            \ either of these directories:",
          D.indent 4 $ D.red $ D.vcat $ map D.fromChars [srcDir1, srcDir2],
          D.reflow $
            "Try to make it so no source directory contains another source directory!"
        ]
    BP_MainPathDuplicate path1 path2 ->
      Help.report
        "CONFUSING FILES"
        Nothing
        "You are telling me to compile these two files:"
        [ D.indent 4 $ D.red $ D.vcat $ map D.fromChars [path1, path2],
          D.reflow $
            if path1 == path2
              then
                "Why are you telling me twice? Is something weird going on with a script?\
                \ I figured I would let you know about it just in case something is wrong.\
                \ Only list it once and you should be all set!"
              else
                "But seem to be the same file though... It makes me think something tricky is\
                \ going on with symlinks in your project, so I figured I would let you know\
                \ about it just in case. Remove one of these files from your command to get\
                \ unstuck!"
        ]
    BP_RootNameDuplicate name outsidePath otherPath ->
      Help.report
        "MODULE NAME CLASH"
        Nothing
        "These two files are causing a module name clash:"
        [ D.indent 4 $ D.red $ D.vcat $ map D.fromChars [outsidePath, otherPath],
          D.reflow $
            "They both say `module "
              ++ ModuleName.toChars name
              ++ " exposing (..)` up\
                 \ at the top, but they cannot have the same name!",
          D.reflow $
            "Try changing to a different module name in one of them!"
        ]
    BP_RootNameInvalid givenPath srcDir _ ->
      Help.report
        "UNEXPECTED FILE NAME"
        Nothing
        "I am having trouble with this file name:"
        [ D.indent 4 $ D.red $ D.fromChars givenPath,
          D.reflow $
            "I found it in your "
              ++ FP.addTrailingPathSeparator srcDir
              ++ " directory\
                 \ which is good, but I expect all of the files in there to use the following\
                 \ module naming convention:",
          toModuleNameConventionTable srcDir ["Main", "HomePage", "Http.Helpers"],
          D.reflow $
            "Notice that the names always start with capital letters! Can you make your file\
            \ use this naming convention?",
          D.toSimpleNote $
            "Having a strict naming convention like this makes it a lot easier to find\
            \ things in large projects. If you see a module imported, you know where to look\
            \ for the corresponding file every time!"
        ]
    BP_CannotLoadDependencies ->
      corruptCacheReport
    BP_Cycle name names ->
      Help.report
        "IMPORT CYCLE"
        Nothing
        "Your module imports form a cycle:"
        [ D.cycle 4 name names,
          D.reflow $
            "Learn more about why this is disallowed and how to break cycles here:"
              ++ D.makeLink "import-cycles"
        ]
    BP_MissingExposed (NE.List (name, problem) _) ->
      case problem of
        Import.NotFound ->
          Help.report
            "MISSING MODULE"
            (Just "geng.toml")
            "The [modules] table of your geng.toml exposes the following module:"
            [ D.indent 4 $ D.red $ D.fromName name,
              D.reflow $
                "But I cannot find it in your src/ directory. Is there a typo? Was it renamed?"
            ]
        Import.Ambiguous _ _ pkg _ ->
          Help.report
            "AMBIGUOUS MODULE NAME"
            (Just "geng.toml")
            "The [modules] table of your geng.toml exposes the following module:"
            [ D.indent 4 $ D.red $ D.fromName name,
              D.reflow $
                "But a module from "
                  ++ Pkg.toChars pkg
                  ++ " already uses that name. Try\
                     \ choosing a different name for your local file."
            ]
        Import.AmbiguousLocal path1 path2 paths ->
          Help.report
            "AMBIGUOUS MODULE NAME"
            (Just "geng.toml")
            "The [modules] table of your geng.toml exposes the following module:"
            [ D.indent 4 $ D.red $ D.fromName name,
              D.reflow $
                "But I found multiple files with that name:",
              D.dullyellow $
                D.indent 4 $
                  D.vcat $
                    map D.fromChars (path1 : path2 : paths),
              D.reflow $
                "Change the module names to be distinct!"
            ]
        Import.AmbiguousForeign _ _ _ ->
          Help.report
            "MISSING MODULE"
            (Just "geng.toml")
            "The [modules] table of your geng.toml exposes the following module:"
            [ D.indent 4 $ D.red $ D.fromName name,
              D.reflow $
                "But I cannot find it in your src/ directory. Is there a typo? Was it renamed?",
              D.toSimpleNote $
                "It is not possible to \"re-export\" modules from other packages. You can only\
                \ expose modules that you define in your own code."
            ]

toModuleNameConventionTable :: FilePath -> [String] -> D.Doc
toModuleNameConventionTable srcDir names =
  let toPair name =
        ( name,
          srcDir </> map (\c -> if c == '.' then FP.pathSeparator else c) name <.> "geng"
        )

      namePairs = map toPair names
      nameWidth = maximum (11 : map (length . fst) namePairs)
      pathWidth = maximum (9 : map (length . snd) namePairs)

      padded width str =
        str ++ replicate (width - length str) ' '

      toRow (name, path) =
        D.fromChars $
          "| " ++ padded nameWidth name ++ " | " ++ padded pathWidth path ++ " |"

      bar =
        D.fromChars $
          "+-" ++ replicate nameWidth '-' ++ "-+-" ++ replicate pathWidth '-' ++ "-+"
   in D.indent 4 $
        D.vcat $
          [bar, toRow ("Module Name", "File Path"), bar] ++ map toRow namePairs ++ [bar]

-- GENERATE

data Generate
  = GenerateCannotLoadArtifacts
  | GenerateCannotOptimizeDebugValues ModuleName.Raw [ModuleName.Raw]
  | GenerateExternUnimplemented [(ModuleName.Raw, N.Name, FilePath)]
  | GenerateTargetRefused Target.Target [Target.Refusal]
  | GenerateNoBackend Target.Target
  | GenerateConstrainedRoots [(ModuleName.Raw, N.Name, [N.Name])]

toGenerateReport :: Generate -> Help.Report
toGenerateReport problem =
  case problem of
    GenerateCannotLoadArtifacts ->
      corruptCacheReport
    GenerateExternUnimplemented problems ->
      Help.report
        "EXTERN HAS NO IMPLEMENTATION"
        Nothing
        "These externs are used by the program, and there is no JavaScript to call for them:"
        [ D.indent 4 $
            D.vcat
              [ D.fromChars $ ModuleName.toChars m ++ "." ++ N.toChars name ++ ": " ++ path ++ " is not in its package"
              | (m, name, path) <- List.sort problems
              ],
          D.reflow
            "A `js` extern is implemented by a plain script, `src/Ext/<Module>.js` in the\
            \ package that declares it, which declares the function the attribute names\
            \ (m1b-extern.md §H15, D198)."
        ]
    GenerateTargetRefused target refusals ->
      Help.report
        "EXTERNS DO NOT SERVE THE TARGET"
        Nothing
        ( "This program is built for the "
            ++ Target.toChars target
            ++ " target, and these modules it is made of have externs with no implementation for it:"
        )
        [ D.indent 4 $ D.vcat $ refusalDocs refusals,
          D.reflow
            "An extern serves the targets of the languages it has rows for: js serves js and\
            \ wasm, erlang serves beam, and c serves native. One with a Geng body as well serves\
            \ every target (ffi.md F1, D77, D222)."
        ]
    GenerateNoBackend target ->
      Help.report
        "NO BACKEND FOR THE TARGET"
        Nothing
        ( "This application's geng.toml builds it for the "
            ++ Target.toChars target
            ++ " target, and this compiler has no backend for it."
        )
        [ D.reflow "It has one backend, which writes JavaScript for the js target."
        ]
    GenerateConstrainedRoots problems ->
      Help.report
        "CONSTRAINED VALUE FOR ERLANG"
        Nothing
        "A build for the beam target exports every value the modules it builds expose, so that Erlang can call it by its name, and these have a constraint:"
        [ D.indent 4 $
            D.vcat
              [ D.fromChars $
                  ModuleName.toChars m
                    ++ "."
                    ++ N.toChars name
                    ++ ", constrained by "
                    ++ List.intercalate ", " (map N.toChars classes)
              | (m, name, classes) <- List.sort problems
              ],
          D.reflow
            "A constrained value is not one Erlang function. Each type the program uses it at\
            \ is a copy of its own, and the value itself wants the class's methods handed to\
            \ it, which nothing outside Geng can build. Expose a wrapper at one type instead,\
            \ such as `sumInts : Array Int -> Int` for `sumAll : Num a => Array a -> a`, and\
            \ leave the constrained value out of the module's `exposing` (m2-interop.md D400)."
        ]
    GenerateCannotOptimizeDebugValues m ms ->
      Help.report
        "DEBUG REMNANTS"
        Nothing
        "There are uses of the `Debug` module in the following modules:"
        [ D.indent 4 $ D.red $ D.vcat $ map (D.fromChars . ModuleName.toChars) (m : ms),
          D.reflow "But the --optimize flag only works if all `Debug` functions are removed!",
          D.toSimpleNote $
            "The issue is that --optimize strips out info needed by `Debug` functions.\
            \ Here are two examples:",
          D.indent 4 $
            D.reflow $
              "(1) It shortens record field names. This makes the generated JavaScript\
              \ smaller, but `Debug.toString` cannot know the real field names anymore.",
          D.indent 4 $
            D.reflow $
              "(2) Values like `type Height = Height Float` are unboxed. This reduces\
              \ allocation, but it also means that `Debug.toString` cannot tell if it is\
              \ looking at a `Height` or `Float` value.",
          D.reflow $
            "There are a few other cases like that, and it will be much worse once we start\
            \ inlining code. That optimization could move `Debug.log` and `Debug.todo` calls,\
            \ resulting in unpredictable behavior. I hope that clarifies why this restriction\
            \ exists!"
        ]

-- CORRUPT CACHE

corruptCacheReport :: Help.Report
corruptCacheReport =
  Help.report
    "CORRUPT CACHE"
    Nothing
    "It looks like some of the information cached in .gren/ has been corrupted."
    [ D.reflow $
        "Try deleting your .gren/ directory to get unstuck.",
      D.toSimpleNote $
        "This almost certainly means that a 3rd party tool (or editor plugin) is\
        \ causing problems your the .gren/ directory. Try disabling 3rd party tools\
        \ one by one until you figure out which it is!"
    ]

-- REPL

data Repl
  = ReplBadDetails Details
  | ReplBadInput BS.ByteString Error.Error
  | ReplBadLocalDeps FilePath Error.Module [Error.Module]
  | ReplProjectProblem BuildProjectProblem
  | ReplBadGenerate Generate
  | ReplBadCache
  | ReplBlocked

replToReport :: Repl -> Help.Report
replToReport problem =
  case problem of
    ReplBadDetails details ->
      toDetailsReport details
    ReplBadInput source err ->
      Help.compilerReport "/" (Error.Module N.replModule "REPL" source err) []
    ReplBadLocalDeps root e es ->
      Help.compilerReport root e es
    ReplProjectProblem projectProblem ->
      toProjectProblemReport projectProblem
    ReplBadGenerate generate ->
      toGenerateReport generate
    ReplBadCache ->
      corruptCacheReport
    ReplBlocked ->
      corruptCacheReport
