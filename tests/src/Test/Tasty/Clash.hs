{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Test.Tasty.Clash where

import           Clash.Annotations.Primitive (HDL(..))
import           Data.Coerce               (coerce)
import           Data.Default              (Default, def)
import qualified Data.List                 as List
import           Data.List                 (intercalate)
import           Data.Maybe                (isJust)
import qualified Data.Text                 as T
import qualified System.Directory          as Directory
import           System.FilePath           ((</>),(<.>))
import           System.IO.Unsafe          (unsafePerformIO)
import           System.IO.Temp            (createTempDirectory, getCanonicalTemporaryDirectory)

import           Test.Tasty
import           Test.Tasty.Program
import           Test.Tasty.Providers
import           Test.Tasty.Runners

import           Test.Tasty.Common
import           Test.Tasty.Ghdl
import           Test.Tasty.Iverilog
import           Test.Tasty.Modelsim
import           Test.Tasty.SymbiYosys

{- Note [copy data files hack]

Clash currently creates a directory for every top entity it synthesizes. For
example, two top entities 'foo' and 'bar' in module FooBar would be synthesized
in the folders:

  $hdldir/FooBar.foo
  $hdldir/FooBar.bar

Any data files used in 'foo' would be copied to its directory, while any data
files used by 'bar' would be copied to  _its_ directory. For example, if 'foo'
and 'bar' would both instantiate a 'blockRamFile' with 'memory_foo.list' and
'memory_bar.list' respectively, the following files would exist after synthesizing:

  $hdldir/FooBar.foo/foo.vhdl
  $hdldir/FooBar.foo/memory_foo.list
  $hdldir/FooBar.bar/bar.vhdl
  $hdldir/FooBar.bar/memory_bar.list

The HDL files (`foo.vhdl` and `bar.vhdl`) would refer to those files relative
to it, for example just "memory_foo.list". Some tools look for these
files relative to the HDL files (most synthesis tools), while others will try to
find them in whatever directory they're executed in (most simulators).

The "hack" in this case refers to copying the files from the HDL directory to
the directory the simulator is run from.

Note: the sensible thing for Clash would be to use relative paths in the HDL
      files as such: `../FooBar.foo/memory_foo.list`. This would satisfy both
      tooling looking relative to HDL files, and tooling run from a sibling
      directory.
-}

data SBuildTarget (target :: HDL) where
  SVHDL          :: SBuildTarget 'VHDL
  SVerilog       :: SBuildTarget 'Verilog
  SSystemVerilog :: SBuildTarget 'SystemVerilog

buildTargetToHdl :: SBuildTarget target -> HDL
buildTargetToHdl SVHDL = VHDL
buildTargetToHdl SVerilog = Verilog
buildTargetToHdl SSystemVerilog = SystemVerilog

-- | Targets to simulate. Defaults to @testBench@.
data BuildTargets
  = BuildAuto
  | BuildSpecific [String]

getBuildTargets :: TestOptions -> [String]
getBuildTargets (TestOptions{buildTargets=BuildSpecific targets}) = targets
getBuildTargets TestOptions{hdlSim, buildTargets=BuildAuto}
  -- We could be clever by adding test bench info to manifest files and
  -- using that in this testsuite
  | hdlSim = ["testBench"]
  | otherwise = ["topEntity"]

-- | Possible verification tools
data VerificationTool = SymbiYosys

data TestOptions =
  TestOptions
    { hdlSim :: Bool
    -- ^ Run hdl simulators (GHDL, ModelSim, etc.)
    , hdlLoad :: Bool
    -- ^ Load hdl into simulator (GHDL, ModelSim, etc.). Disabling this will
    -- disable 'hdlSim' too.
    , expectSimFail :: Maybe (TestExitCode, T.Text)
    -- ^ Expect simulation to fail: Nothing if simulation is expected to run
    -- without errors, or Just (part of) the error message the simulation is
    -- expected to throw.
    , verificationTool :: Maybe VerificationTool
    -- ^ A formal verification tool with which to attempt to verify
    -- the generated hdl
    , expectVerificationFail :: Maybe (TestExitCode, T.Text)
    -- ^ Expect the verifier to fail: Nothing if verification should succeed,
    -- or Just (part of) the error message Clash is expected to throw.
    , expectClashFail :: Maybe (TestExitCode, T.Text)
    -- ^ Expect Clash to fail: Nothing if Clash is expected to compile without
    -- errors, or Just (part of) the error message Clash is expected to throw.
    , hdlTargets :: [HDL]
    -- ^ Run tests for these targets
    , ghcFlags :: [String]
    -- ^ Extra flags to pass to GHC
    , clashFlags :: [String]
    -- ^ Extra flags to pass to Clash
    , buildTargets :: BuildTargets
    -- ^ Indicates what should be built to an executable. Defaults to @["testBench"]@
    -- if 'hdlSim' is set, otherwise @["topEntity"]@.
    , vvpStderrEmptyFail :: Bool
    -- ^ Whether an empty stderr means test failure when running VVP
    }

allTargets :: [HDL]
allTargets = [VHDL, Verilog, SystemVerilog]

instance Default TestOptions where
  def =
    TestOptions
      { hdlSim=True
      , hdlLoad=True
      , expectClashFail=Nothing
      , expectSimFail=Nothing
      , expectVerificationFail=Nothing
      , verificationTool=Nothing
      , hdlTargets=allTargets
      , ghcFlags=[]
      , clashFlags=[]
      , buildTargets=BuildAuto
      , vvpStderrEmptyFail=True
      }

-- | Directory where testbenches live.
sourceDirectory :: String
sourceDirectory =
  -- TODO: Allow testsuite to be run from any directory. This is easy from the
  -- clash-testsuite side, as we can add
  --
  --     data-files:
  --       shouldfail/**/*.hs
  --       shouldwork/**/*.hs
  --
  -- to the cabal file, then use Paths_clash_testsuite to get access to the
  -- data directory / data files. However, invoking clash for building in the
  -- testsuite requires the location of primitives to be known and accessible
  -- by clash (clash will automatically search in clash-lib/prims, which is
  -- why running from the project root works). Getting these would require
  -- exporting Paths_clash_lib from clash-lib, which might be grimy or not
  -- possible when using stack instead of cabal. Someone should investigate
  unsafePerformIO Directory.getCurrentDirectory
{-# NOINLINE sourceDirectory #-}

-- | Gather all files with specific extension
hdlFiles
  :: String
  -- ^ Extension
  -> FilePath
  -- ^ Directory to search
  -> FilePath
  -- ^ Subdirectory to search
  -> IO [FilePath]
  -- ^ Files with subdirectory as prefix
hdlFiles ext dir subdir = do
  allFiles <- Directory.getDirectoryContents (dir </> subdir)
  return $ map (subdir </>) (filter (List.isSuffixOf ext) allFiles)
{-# NOINLINE hdlFiles #-}

-- | Given a number of test trees, make sure each one of them is executed
-- one after the other. To prevent naming collisions, parent group names can
-- be included. Parent group names should be ordered outer -> inner.
sequenceTests
  :: [TestName]
  -- ^ Parent group names
  -> [(TestName, TestTree)]
  -- ^ Tests to sequence
  -> [TestTree]
sequenceTests path (unzip -> (testNames, testTrees)) =
  zipWith applyAfter testPatterns testTrees
    where
      -- Make pattern for a single test
      pat :: TestName -> String
      pat nm = "$0 ~ /" ++ intercalate "." (reverse (nm:path)) ++ "/"

      -- Test patterns for all given tests such that each executes sequentially
      testPatterns = init (map (fmap pat) (Nothing : map Just testNames))

      -- | Generate pattenrs given parent patterns and item patterns
      applyAfter :: Maybe String -> TestTree -> TestTree
      applyAfter Nothing  tt = tt
      applyAfter (Just p) tt = after AllSucceed p tt

data ClashGenTest = ClashGenTest
  { cgExpectFailure :: Maybe (TestExitCode, T.Text)
    -- ^ Expected failure code and output (if any)
  , cgBuildTarget :: HDL
  , cgSourceDirectory :: FilePath
  , cgExtraArgs :: [String]
  , cgModName :: String
  , cgOutputDirectory :: IO FilePath
  }

instance IsTest ClashGenTest where
  run optionSet ClashGenTest{..} progressCallback = do
    oDir <- cgOutputDirectory
    case cgExpectFailure of
      Nothing -> run optionSet (program oDir) progressCallback
      Just exit -> run optionSet (failingProgram oDir exit) progressCallback
   where
    program oDir =
      TestProgram "clash" (args oDir) NoGlob PrintNeither False Nothing

    failingProgram oDir (testExit, expectedErr) =
      TestFailingProgram
        (testExitCode testExit) "clash" (args oDir) NoGlob PrintNeither False
        (specificExitCode testExit) (ExpectStdErr expectedErr) Nothing

    args oDir =
      [ target
      , "-i" <> cgSourceDirectory
      , cgModName
      , "-fclash-hdldir", oDir
      , "-odir", oDir
      , "-hidir", oDir
      , "-fclash-debug", "DebugSilent"
      ] <> cgExtraArgs

    target =
      case cgBuildTarget of
        VHDL          -> "--vhdl"
        Verilog       -> "--verilog"
        SystemVerilog -> "--systemverilog"

  testOptions = coerce (testOptions @TestProgram)

data ClashBinaryTest = ClashBinaryTest
  { cbBuildTarget :: HDL
  , cbSourceDirectory :: FilePath
  , cbExtraBuildArgs :: [String]
  , cbExtraExecArgs :: [String]
  , cbModName :: String
  , cbOutputDirectory :: IO FilePath
  }

instance IsTest ClashBinaryTest where
  run optionSet ClashBinaryTest{..} progressCallback = do
    oDir <- cbOutputDirectory
    buildRes <- run optionSet (buildProgram oDir) progressCallback

    if resultSuccessful buildRes
      then run optionSet (execProgram oDir) progressCallback
      else pure buildRes
   where
    buildProgram oDir =
      TestProgram "clash" (buildArgs oDir) NoGlob PrintStdErr False Nothing

    buildArgs oDir =
      [ "-package", "clash-testsuite"
      , "-main-is", cbModName <> ".main" <> show cbBuildTarget
      , "-o", oDir </> "out"
      , "-outputdir", oDir
      ] <> cbExtraBuildArgs <>
      [ cbSourceDirectory </> cbModName <.> "hs"
      ]

    execProgram oDir =
      TestProgram (oDir </> "out") (oDir:cbExtraExecArgs) NoGlob PrintStdErr False Nothing

  testOptions = coerce (testOptions @TestProgram)

-- | Generate two test trees for testing VHDL: one for building designs and one
-- for running them. Depending on 'hdlSim' the latter will be executed or not.
vhdlTests
  :: TestOptions
  -> IO FilePath
  -> ( [(TestName, TestTree)] -- build tests
     , [(TestName, TestTree)] -- simulation tests
     )
vhdlTests opts@TestOptions{..} tmpDir = (buildTests, simTests)
 where
  importName = "GHDL (import)"
  makeName t = "GHDL (make " <> t <> ")"
  buildTests = concat
    [ [ (importName, singleTest importName (GhdlImportTest tmpDir)) ]
    , [ (makeName t, singleTest (makeName t) (GhdlMakeTest tmpDir t))
      | t <- getBuildTargets opts ]
    ]

  simName t = "GHDL (sim " <> t <> ")"
  simTests =
    [ (simName t, singleTest (simName t) (GhdlSimTest expectSimFail tmpDir t))
    | t <- getBuildTargets opts
    ]

-- | Generate two test trees for testing Verilog: one for building designs and one
-- for running them. Depending on 'hdlSim' the latter will be executed or not.
verilogTests
  :: TestOptions
  -> IO FilePath
  -> ( [(TestName, TestTree)] -- build tests
     , [(TestName, TestTree)] -- simulation tests
     )
verilogTests opts@TestOptions{..} tmpDir = (buildTests, simTests)
 where
  makeName t = "iverilog (make " <> t <> ")"
  buildTests =
    [ (makeName t, singleTest (makeName t) (IVerilogMakeTest tmpDir t))
    | t <- getBuildTargets opts ]

  simName t = "iverilog (sim " <> t <> ")"
  simTests =
    [ (simName t, singleTest (simName t) (IVerilogSimTest expectSimFail vvpStderrEmptyFail tmpDir t))
    | t <- getBuildTargets opts ]

-- | Generate two test trees for testing SystemVerilog: one for building designs and
-- one for running them. Depending on 'hdlSim' the latter will be executed or not.
systemVerilogTests
  :: TestOptions
  -> IO FilePath
  -> ( [(TestName, TestTree)] -- build tests
     , [(TestName, TestTree)] -- simulation tests
     )
systemVerilogTests opts@TestOptions{..} tmpDir = (buildTests, simTests)
 where
  vlibName = "modelsim (vlib)"
  vlogName = "modelsim (vlog)"
  buildTests =
    [ (vlibName, singleTest vlibName (ModelsimVlibTest tmpDir))
    , (vlogName, singleTest vlogName (ModelsimVlogTest tmpDir))
    ]

  simName t = "modelsim (sim " <> t <> ")"
  simTests =
    [ (simName t, singleTest (simName t) (ModelsimSimTest expectSimFail tmpDir t))
    | t <- getBuildTargets opts ]

-- | Generate a test tree for running SymbiYosys
sbyTests :: TestOptions -> IO FilePath -> ([(TestName, TestTree)])
sbyTests opts@TestOptions {..} tmpDir =
  [ ( "SymbiYosys"
    , singleTest "SymbiYosys"
                 (SbyVerificationTest expectVerificationFail tmpDir t)
    )
  | t <- getBuildTargets opts
  ]

runTest1
  :: String
  -> TestOptions
  -> [TestName]
  -> HDL
  -> TestTree
runTest1 modName opts@TestOptions{..} path target =
  withResource mkTmpDir Directory.removeDirectoryRecursive $ \tmpDir -> do
    testGroup (show target) $ sequenceTests (show target:path) $ clashTest tmpDir :
      (case target of
        VHDL -> buildAndSimTests (vhdlTests opts tmpDir)
        Verilog -> buildAndSimTests (verilogTests opts tmpDir)
        SystemVerilog-> buildAndSimTests (systemVerilogTests opts tmpDir)
      ) <>
      (case verificationTool of
         Nothing -> []
         Just SymbiYosys -> sbyTests opts tmpDir
      )

 where
  mkTmpDir = flip createTempDirectory "clash-test" =<< getCanonicalTemporaryDirectory
  sourceDir = List.foldl' (</>) sourceDirectory (reverse (tail path))

  clashTest tmpDir =
    ("clash (gen)", singleTest "clash (gen)" (ClashGenTest {
      cgExpectFailure=expectClashFail
    , cgBuildTarget=target
    , cgSourceDirectory=sourceDir
    , cgExtraArgs=clashFlags
    , cgModName=modName
    , cgOutputDirectory=tmpDir
    }))

  buildAndSimTests (buildTests, simTests) =
    case (isJust expectClashFail, hdlLoad, hdlSim) of
      (True, _, _) -> []
      (_, False, _) -> []
      (_, _, False) -> buildTests
      _ -> buildTests <> simTests

runTest
  :: String
  -- ^ Name of test
  -> TestOptions
  -> [TestName]
  -- ^ Parent test names in order of distance to the test. That is, the last
  -- item in the list will be the root node, while the first one will be the
  -- one closest to the test. Should correspond to directories on filesystem.
  -> TestTree
runTest modName opts path =
  testGroup modName (map (runTest1 modName opts (modName:path)) (hdlTargets opts))

outputTest'
  :: String
  -- ^ Module name
  -> HDL
  -- ^ Build target
  -> [String]
  -- ^ Extra Clash arguments
  -> [String]
  -- ^ Extra GHC arguments
  -> [TestName]
  -- ^ Parent test names in order of distance to the test. That is, the last
  -- item in the list will be the root node, while the first one will be the
  -- one closest to the test.
  -> TestTree
outputTest' modName target extraClashArgs extraGhcArgs path =
  withResource mkTmpDir Directory.removeDirectoryRecursive $ \tmpDir ->
    testGroup (show target) $ sequenceTests (show target : path) $
      [ clashGenHdl tmpDir
      , clashBuild tmpDir
      ]
 where
  mkTmpDir = flip createTempDirectory "clash-test" =<< getCanonicalTemporaryDirectory
  sourceDir = List.foldl' (</>) sourceDirectory (reverse (tail path))

  clashGenHdl workDir = ("clash (gen)", singleTest "clash (gen)" (ClashGenTest {
      cgExpectFailure=Nothing
    , cgBuildTarget=target
    , cgSourceDirectory=sourceDir
    , cgExtraArgs=extraClashArgs
    , cgModName=modName
    , cgOutputDirectory=workDir
    }))

  clashBuild workDir = ("clash (exec)", singleTest "clash (exec)" (ClashBinaryTest {
      cbBuildTarget=target
    , cbSourceDirectory=sourceDir
    , cbExtraBuildArgs="-DOUTPUTTEST" : extraGhcArgs
    , cbExtraExecArgs=[]
    , cbModName=modName
    , cbOutputDirectory=workDir
    }))

outputTest
  :: String
  -- ^ Module name
  -> TestOptions
  -> [TestName]
  -- ^ Parent test names in order of distance to the test. That is, the last
  -- item in the list will be the root node, while the first one will be the
  -- one closest to the test.
  -> TestTree
outputTest modName opts path =
  let testName = modName ++ " [output test]"
   in testGroup testName
        [ outputTest' modName target (clashFlags opts) (ghcFlags opts) (testName:path)
        | target <- hdlTargets opts
        ]

clashLibTest'
  :: String
  -- ^ Module name
  -> HDL
  -- ^ Build target
  -> [String]
  -- ^ Extra GHC arguments
  -> [TestName]
  -- ^ Parent test names in order of distance to the test. That is, the last
  -- item in the list will be the root node, while the first one will be the
  -- one closest to the test.
  -> TestTree
clashLibTest' modName target extraGhcArgs path =
  withResource mkTmpDir Directory.removeDirectoryRecursive $ \tmpDir ->
    testGroup (show target) $ sequenceTests (show target : path) $
      [ clashBuild tmpDir
      ]
 where
  mkTmpDir = flip createTempDirectory "clash-test" =<< getCanonicalTemporaryDirectory
  sourceDir = List.foldl' (</>) sourceDirectory (reverse (tail path))

  clashBuild workDir = ("clash (exec)", singleTest "clash (exec)" (ClashBinaryTest {
      cbBuildTarget=target
    , cbSourceDirectory=sourceDir
    , cbExtraBuildArgs="-DCLASHLIBTEST" : extraGhcArgs
    , cbExtraExecArgs=[]
    , cbModName=modName
    , cbOutputDirectory=workDir
    }))

clashLibTest
  :: String
  -- ^ Module name
  -> TestOptions
  -> [TestName]
  -- ^ Parent test names in order of distance to the test. That is, the last
  -- item in the list will be the root node, while the first one will be the
  -- one closest to the test.
  -> TestTree
clashLibTest modName opts path =
  -- HACK: clashLibTests are run sequentially to prevent race issues. See:
  -- HACK: https://github.com/clash-lang/clash-compiler/pull/1416
  let testName = modName ++ " [clash-lib test]"
   in testGroup testName $ sequenceTests (testName:path)
        [ (show target, clashLibTest' modName target (ghcFlags opts) (testName:path))
        | target <- hdlTargets opts
        ]
