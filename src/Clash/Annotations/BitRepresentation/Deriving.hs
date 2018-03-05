{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveLift #-}

module Clash.Annotations.BitRepresentation.Deriving
  ( deriveDefaultAnnotation
  , deriveBitPack
  ) where

import GHC.Exts
import GHC.Integer.Logarithms

import Control.Monad (zipWithM)

import Data.List (mapAccumL)
import Data.Bits (shiftL, shiftR)
import Data.Proxy (Proxy(..))
import Data.Maybe (catMaybes, fromJust)

import qualified Data.Map as Map
import qualified Data.Text.Lazy as Text

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import GHC.TypeLits (natVal)

import Clash.Sized.BitVector (BitVector(..), high, low)
import Clash.Class.Resize  (resize)
import Clash.Class.BitPack (BitPack, BitSize, pack)
import Clash.Annotations.BitRepresentation ( DataReprAnn(..)
                                           , DataRepr'(..)
                                           , ConstrRepr'(..)
                                           , ConstrRepr(..)
                                           , reprType
                                           , thTypeToType'
                                           , dataReprAnnToDataRepr'
                                           )

import Clash.Annotations.BitRepresentation.Util ( bitOrigins
                                                , BitOrigin(..)
                                                , bitRanges
                                                , Bit(..)
                                                )

type NameMap = Map.Map Name Type


integerLog2Ceil :: Integer -> Integer
integerLog2Ceil n =
  let nlog2 = fromIntegral $ I# (integerLog2# n) in
  if n > 2^nlog2 then nlog2 + 1 else nlog2

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV n) = n
tyVarBndrName (KindedTV n _k) = n

-- | Replace Vars types given in mapping
resolve :: NameMap -> Type -> Type
resolve nmap (VarT n) = nmap Map.! n
resolve nmap (AppT t1 t2) = AppT (resolve nmap t1) (resolve nmap t2)
resolve _nmap t@(ConT _) = t
resolve _nmap t = error $ {-$(curLoc) ++-} "Unexpected type: " ++ show t

resolveCon :: NameMap -> Con -> Con
resolveCon nmap (NormalC t (unzip -> (bangs, fTypes))) =
  NormalC t $ zip bangs $ map (resolve nmap) fTypes
resolveCon _name constr =
  error $ {-$(curLoc) ++-} "Unexpected constructor: " ++ show constr

collectTypeArgs :: Type -> (Type, [Type])
collectTypeArgs t@(ConT _name) = (t, [])
collectTypeArgs (AppT t1 t2) =
  let (base, args) = collectTypeArgs t1 in
  (base, args ++ [t2])
collectTypeArgs t =
  error $ {-$(curLoc) ++-} "Unexpected type: " ++ show t

typeSize :: Type -> Q Exp
typeSize typ = do
  bitSizeInstances <- reifyInstances ''BitSize [typ]
  case bitSizeInstances of
    [] ->
      error $ {-$(curLoc) ++ -} unwords [
          "Could not find custom bit representation nor BitSize instance"
        , "for", show typ ++ "." ]
    [TySynInstD _ (TySynEqn _ (LitT (NumTyLit n)))] ->
      [| n |]
    [_impl] ->
      [| natVal (Proxy :: Proxy (BitSize $(return typ))) |]
    unexp ->
      error $ {-$(curLoc) ++ -} "Unexpected result from reifyInstances: " ++ show unexp

bitmask
  :: Integer
  -> Integer
  -> Integer
bitmask _start 0    = 0
bitmask start  size = shiftL (2^size - 1) $ fromIntegral (start - (size - 1))

buildConstrRepr
  :: Q Exp
  -- ^ Data size
  -> Integer
  -- ^ Number of bits reserved for constructor
  -> Name
  -- ^ Constr name
  -> [Exp]
  -- ^ Field sizes
  -> Integer
  -- ^ Constructor number
  -> Q Exp
buildConstrRepr dataSize constrSize constrName fieldSizes constrN = [|
  ConstrRepr
    constrName
    $mask
    $value
    $(ListE <$> fanns)
  |]
  where
    mask  = [| bitmask ($dataSize - 1) constrSize |]
    value = [| shiftL constrN (fromIntegral $ $dataSize - 1)|]
    fanns =
      sequence $ snd
               $ mapAccumL
                    (\start size -> ([| $start - $size |], [| bitmask $start $size |]))
                    [| $dataSize - constrSize - 1 |]
                    (map return fieldSizes)


fieldTypes :: Con -> [Type]
fieldTypes (NormalC _nm bTys) =
  [ty | (_, ty) <- bTys]
fieldTypes (RecC _nm bTys) =
  [ty | (_, _, ty) <- bTys]
fieldTypes (InfixC (_, ty1) _nm (_, ty2)) =
  [ty1, ty2]
fieldTypes con =
  error $ {-$(curLoc) ++-} "Unexpected constructor type: " ++ show con

conName :: Con -> Name
conName c = case c of
  NormalC nm _  -> nm
  RecC    nm _  -> nm
  InfixC _ nm _ -> nm
  _ -> error $ {-$(curLoc) ++-} "No GADT support"

constrFieldSizes
  :: Con
  -> Q (Name, [Exp])
constrFieldSizes con = do
  fieldSizes <- mapM typeSize (fieldTypes con)
  return (conName con, fieldSizes)

-- | Derive DataRepr' for a specific type.
deriveDataRepr :: Type -> Q Exp
deriveDataRepr typ = do
  info <- reify tyConstrName
  case info of
    (TyConI (DataD [] _constrName vars _kind dConstructors _clauses)) ->
      let varMap = Map.fromList $ zip (map tyVarBndrName vars) typeArgs in
      let resolvedConstructors = map (resolveCon varMap) dConstructors in do

      -- Get sizes and names of all constructors
      (constrNames, fieldSizess) <-
        unzip <$> (mapM constrFieldSizes resolvedConstructors)

      let fieldSizess'  = ListE <$> fieldSizess
      let fieldSizess'' = ListE fieldSizess'

      -- Determine size of whole datatype
      let constructorSizes = [| map sum $(return fieldSizess'') |]
      let constrSize = integerLog2Ceil (fromIntegral $ length dConstructors)
      let dataSize = [| constrSize + (maximum $constructorSizes) |]

      -- Determine at which bits various fields start
      let constrReprs = zipWith3
                          (buildConstrRepr dataSize constrSize)
                          constrNames
                          fieldSizess
                          [0..]

      [| DataReprAnn $(reprType $ return typ)  $dataSize $(listE constrReprs)  |]
    _ ->
      error $ {-$(curLoc) ++-} "Could not derive dataRepr for: " ++ show info

    where
      (ConT tyConstrName, typeArgs) = collectTypeArgs typ

-- | Collect data reprs of current module
collectDataReprs :: Q [DataRepr']
collectDataReprs = do
  thisMod <- thisModule
  map dataReprAnnToDataRepr' <$> reifyAnnotations (AnnLookupModule thisMod)

group :: [Bit] -> [(Int, Bit)]
group [] = []
group bs = (length head', head bs) : rest
  where
    tail' = dropWhile (==head bs) bs
    head' = takeWhile (==head bs) bs
    rest  = group tail'

bitToExpr' :: (Int, Bit) -> Q Exp
bitToExpr' (0, _) = error $ {-$(curLoc) ++-} "Unexpected group length: 0"
bitToExpr' (1, H) = lift high
bitToExpr' (1, L) = lift low
bitToExpr' (1, _) = lift low
bitToExpr' (numTyLit' -> n, H) =
  [| complement (resize $(lift low) :: BitVector $n) |]
bitToExpr' (numTyLit' -> n, L) =
  [| resize $(lift low) :: BitVector $n |]
bitToExpr' (numTyLit' -> n, _) =
  [| resize $(lift low) :: BitVector $n |]

bitsToExpr :: [Bit] -> Q Exp
bitsToExpr [] = error $ {-$(curLoc) ++-} "Unexpected empty bit list"
bitsToExpr bits =
  foldl1
    (\v1 v2 -> [| $v1 ++# $v2 |])
    (map bitToExpr' $ group bits)

numTyLit' n = LitT <$> (numTyLit $ fromIntegral n)

-- | Select a list of ranges from a bitvector expression
select'
  :: Exp
  -> [(Int, Int)]
  -> Q Exp
select' _vec [] =
  error $ {-$(curLoc) ++ -}"Unexpected empty list of intervals"
select' vec ranges =
  foldl1 (\v1 v2 -> [| $v1 ++# $v2 |]) $ map (return . select'') ranges
    where
      select'' :: (Int, Int) -> Exp
      select'' (from, downto) =
        let size = from - downto + 1 in
        let
          shifted
            | downto == 0 =
                vec
            | otherwise =
                AppE
                  (AppE (VarE 'shiftR) vec)
                  (LitE $ IntegerL $ fromIntegral downto) in

        SigE
          -- Select from whole vector
          (AppE (VarE 'resize) shifted)
          -- Type signature:
          (AppT (ConT ''BitVector) (LitT $ NumTyLit $ fromIntegral size))

-- | Select a range (bitorigin) from a bitvector
select
  :: [Exp]
  -- ^ BitVectors of fields
  -> BitOrigin
  -- ^ Select bits
  -> Q Exp
select fields (Lit []) =
  error $ {-$(curLoc) ++-} "Unexpected empty literal."
select fields (Lit lits) = do
  let size = fromIntegral $ length lits
  vec <- bitsToExpr lits
  return $ SigE
            -- Apply bLit to literal string
            vec
            -- Type signature:
            (AppT (ConT ''BitVector) (LitT $ NumTyLit size))

select fields (Field fieldn from downto) =
  select' (fields !! fieldn) [(from, downto)]

buildPackMatch
  :: Integer
  -> ConstrRepr'
  -> Q Match
buildPackMatch dataSize constrRepr@(ConstrRepr' qName constrN mask value fieldanns) = do
  constr <- fromJust <$> lookupValueName (Text.unpack qName)

  fieldNames <-
    mapM (\n -> newName $ "field" ++ show n) [0..length fieldanns-1]
  fieldPackedNames <-
    mapM (\n -> newName $ "fieldPacked" ++ show n) [0..length fieldanns-1]

  let packed fName = AppE (VarE 'pack) (VarE fName)
  let pack' pName fName = ValD (VarP pName) (NormalB $ packed fName) []
  let fieldPackedDecls = zipWith pack' fieldPackedNames fieldNames
  let origins = bitOrigins (fromIntegral dataSize) (mask, value, fieldanns)

  vec <- foldl1
              (\v1 v2 -> [| $v1 ++# $v2 |])
              (map (select $ map VarE fieldPackedNames) origins)

  return $ Match (ConP constr (VarP <$> fieldNames)) (NormalB vec) fieldPackedDecls

-- | Build a /pack/ function corresponding to given DataRepr
buildPack
  :: Type
  -> DataRepr'
  -> Q [Dec]
buildPack argTy dataRepr@(DataRepr' _name size constrs) = do
  argName      <- newName "toBePacked"
  let resTy     = AppT (ConT ''BitVector) (LitT $ NumTyLit size)
  let funcName  = mkName "pack"
  let funcSig   = SigD funcName (AppT (AppT ArrowT argTy) resTy)
  constrs'     <- mapM (buildPackMatch size) constrs
  let body      = CaseE (VarE argName) constrs'
  let func      = FunD funcName [Clause [VarP argName] (NormalB body) []]
  return $ [funcSig, func]

buildUnpackField
  :: Name
  -> Integer
  -> Q Exp
buildUnpackField valueName mask =
  let ranges = bitRanges mask in
  let vec = select' (VarE valueName) ranges in
  [| unpack $vec |]

buildUnpackIfE
  :: Name
  -> Integer
  -> ConstrRepr'
  -> Q (Guard, Exp)
buildUnpackIfE valueName dataSize constrRepr@(ConstrRepr' qName constrN mask value fieldanns) = do
  let valueName' = return $ VarE valueName
  constr <- ConE <$> (fromJust <$> (lookupValueName (Text.unpack qName)))
  guard  <- NormalG <$> [| ((.&.) $valueName' mask) == value |]
  fields <- mapM (buildUnpackField valueName) fieldanns
  return $ (guard, foldl AppE constr fields)

---- | Build an /unpack/ function corresponding to given DataRepr
buildUnpack
  :: Type
  -> DataRepr'
  -> Q [Dec]
buildUnpack resTy dataRepr@(DataRepr' _name size constrs) = do
  argName <- newName "toBeUnpacked"
  let funcName = mkName "unpack"
  let argTy    = AppT (ConT ''BitVector) (LitT $ NumTyLit size)
  let funcSig  = SigD funcName (AppT (AppT ArrowT argTy) resTy)
  matches     <- mapM (buildUnpackIfE argName size) constrs
  err         <- [| error $ "Could not match constructor for: " ++ show $(varE argName) |]
  let body     = MultiIfE $ matches ++ [(NormalG (ConE 'True), err)]
  let func     = FunD funcName [Clause [VarP argName] (NormalB body) []]
  return $ [funcSig, func]

deriveDefaultAnnotation :: Q Type -> Q [Dec]
deriveDefaultAnnotation typ =
  return <$> pragAnnD ModuleAnnotation (deriveDataRepr =<< typ)

-- | Derives BitPack instances for given type. Will account for custom bit
-- representation annotations in the module where the splice is ran. Note that
-- the generated instance might conflict with existing implementations (for
-- example, an instance for /Maybe a/ exists, yielding conflicts for any
-- alternative implementations).
deriveBitPack :: Q Type -> Q [Dec]
deriveBitPack typQ = do
  anns <- collectDataReprs
  typ  <- typQ
  typ' <- (return . thTypeToType') =<< typQ

  let ann = case filter (\(DataRepr' t _ _) -> t == typ') anns of
              [a] -> a
              []  -> error $ {-$(curLoc) ++-} "No custom bit annotation found."
              _   -> error $ {-$(curLoc) ++-} "Overlapping bit annotations found."

  packFunc   <- buildPack typ ann
  unpackFunc <- buildUnpack typ ann

  let (DataRepr' _name dataSize _constrs) = ann

  let bitSizeInst = TySynInstD
                      ''BitSize
                      (TySynEqn
                        [typ]
                        (LitT (NumTyLit $ fromIntegral dataSize)))

  let bpInst = [ InstanceD
                   (Just Overlapping)
                   -- ^ Overlap
                   []
                   -- ^ Context
                   (AppT (ConT ''BitPack) typ)
                   -- ^ Type
                   (bitSizeInst : packFunc ++ unpackFunc)
                   -- ^ Declarations
               ]
  alreadyIsInstance <- isInstance ''BitPack [typ]
  if alreadyIsInstance then
    error $ show typ ++ " already has a BitPack instance."
  else
    return bpInst
