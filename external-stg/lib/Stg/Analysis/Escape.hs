module Stg.Analysis.Escape where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Stg.Syntax
import Stg.Pretty
import qualified Data.ByteString.Char8 as BS

data EscapeInfo = Escapes | Doesn'tEscape deriving (Eq, Show)
data EscapeType = SideEffect | Escaping | ValueEscaping | Referred deriving (Eq, Show)

escapeInfo :: EscapeType -> EscapeInfo
escapeInfo Escaping = Escapes
escapeInfo _ = Doesn'tEscape

type Escapees = Map.Map Binder EscapeType

emptyEscapees :: Escapees
emptyEscapees = Map.empty

mkEscapees :: [(Binder, EscapeType)] -> Escapees
mkEscapees = Map.fromList

extendEscapees :: Escapees -> Binder -> EscapeType -> Escapees
extendEscapees esc i t = Map.insertWith lubEscapeType i t esc

extendEscapeesList :: Escapees -> [(Binder, EscapeType)] -> Escapees
extendEscapeesList esc ((i, t):es) = extendEscapeesList (extendEscapees esc i t) es
extendEscapeesList esc [] = esc

unionEscapees :: Escapees -> Escapees -> Escapees
unionEscapees = Map.unionWith lubEscapeType

lubEscapeType :: EscapeType -> EscapeType -> EscapeType
lubEscapeType SideEffect _ = SideEffect
lubEscapeType _ SideEffect = SideEffect
lubEscapeType Escaping _ = Escaping
lubEscapeType _ Escaping = Escaping
lubEscapeType ValueEscaping _ = ValueEscaping
lubEscapeType _ ValueEscaping = ValueEscaping
lubEscapeType _ _ = Referred

alterEscapeType :: EscapeType -> EscapeType -> EscapeType
alterEscapeType t SideEffect = SideEffect
alterEscapeType t _ = t

mergeEscapees :: EscapeType -> Escapees -> Escapees -> Escapees
mergeEscapees SideEffect body rhs = body `unionEscapees` fmap (const SideEffect) rhs
mergeEscapees Escaping body rhs = body `unionEscapees` fmap (alterEscapeType Escaping) rhs
mergeEscapees Referred body rhs = body `unionEscapees` fmap (alterEscapeType Referred) rhs
mergeEscapees ValueEscaping body rhs = body `unionEscapees` rhs

delEscapee :: Escapees -> Binder -> Escapees
delEscapee esc i = Map.delete i esc

delEscapees :: Escapees -> [Binder] -> Escapees
delEscapees = foldl delEscapee

lookupEscapee :: Escapees -> Binder -> Maybe EscapeType
lookupEscapee esc i = Map.lookup i esc

escapes :: EscapeType -> Bool
escapes SideEffect = True
escapes Escaping = True
escapes _ = False

data Signature = Signature [EscapeType] | NoneEscape

instance Eq Signature where
  Signature flags1 == Signature flags2 = flags1 == flags2
  Signature flags == NoneEscape = False
  NoneEscape == Signature flags = False
  NoneEscape == NoneEscape = True

data EscapeEnv = EscapeEnv {
    signatures :: Map.Map Name Signature
  , insideLetNoEscapeBody :: Map.Map Binder (Set.Set Binder)
} deriving (Eq)

emptyEscapeEnv :: EscapeEnv
emptyEscapeEnv = EscapeEnv {signatures = Map.empty, insideLetNoEscapeBody = Map.empty}

extendEscapeEnv :: EscapeEnv -> Binder -> Signature -> EscapeEnv
extendEscapeEnv EscapeEnv{signatures = s, insideLetNoEscapeBody = lne} i sig =
  EscapeEnv {
      signatures = Map.insert (binderUniqueName i) sig s
    , insideLetNoEscapeBody = fmap (Set.insert i) lne
  }

addLneEscapeEnv :: EscapeEnv -> Binder -> EscapeEnv
addLneEscapeEnv env@EscapeEnv{insideLetNoEscapeBody = lne} i = env{insideLetNoEscapeBody = Map.insert i Set.empty lne}

delEscapeEnv :: EscapeEnv -> Binder -> EscapeEnv
delEscapeEnv EscapeEnv{signatures = s, insideLetNoEscapeBody = lne} i =
  EscapeEnv {
      signatures = Map.delete (binderUniqueName i) s
    , insideLetNoEscapeBody = (fmap (Set.delete i) . Map.delete i) lne
  }

delEscapeEnvList :: EscapeEnv -> [Binder] -> EscapeEnv
delEscapeEnvList = foldl delEscapeEnv

lookupSignature :: EscapeEnv -> Binder -> Maybe Signature
lookupSignature env i = Map.lookup (binderUniqueName i) (signatures env)

lookupJoinPoint :: EscapeEnv -> Binder -> Maybe (Set.Set Binder)
lookupJoinPoint env i = Map.lookup i (insideLetNoEscapeBody env)

varsFromArgs :: [Arg] -> [Binder]
varsFromArgs ((StgVarArg i):args) = i : varsFromArgs args
varsFromArgs (_:args) = varsFromArgs args
varsFromArgs [] = []

escapeAnalysis :: EscapeEnv -> Module -> (Set.Set Binder, EscapeEnv)
escapeAnalysis initEnv mod = (foldl Set.union Set.empty escList, envFinal)
  where
    (escList, envFinal) = (escapeAnalysis' initEnv . bindings . moduleTopBindings) mod
    escapeAnalysis' env (bind:binds) = (escFinal : escTail, envTail)
      where
        (escTail, envTail) = escapeAnalysis' env' binds
        (_, env', escFinal) = case bind of
            StgNonRec _ _ -> escapeesBinding emptyEscapees envInit bind (StgLit LitNullAddr) False
            StgRec _ -> escapeesFix emptyEscapees envInit
          where
            escapeesFix :: Escapees -> EscapeEnv -> (Escapees, EscapeEnv, Set.Set Binder)
            escapeesFix escTmp envTmp
              | envTmp' == envTmp && escTmp' == escTmp = result
              | otherwise = escapeesFix escTmp' envTmp'
              where
                result@(escTmp', envTmp', _) = escapeesBinding escTmp envTmp bind (StgLit LitNullAddr) False
            envInit = env `extendEnvBindInit` bind
    escapeAnalysis' env [] = ([], env)
    bindings ((StgTopLifted b):bs) = b : bindings bs
    bindings (_:bs) = bindings bs
    bindings [] = []

escapees :: EscapeEnv -> Expr -> (Escapees, Set.Set Binder)

escapees env (StgLet bind body) = escapeesLet env bind body False

escapees env (StgLetNoEscape bind body) = escapeesLet env bind body True

escapees env (StgCase scrut b _ alts) =
    case escTypeCaseBinder `lubEscapeType` escTypeAltConBinders of
      Referred -> (mergeEscapees Referred unionEscAlts escScrut `delEscapee` b, escFinal')
      SideEffect -> (mergeEscapees SideEffect unionEscAlts escScrut `delEscapee` b, escFinal')
      _ -> ((unionEscAlts `unionEscapees` escScrut) `delEscapee` b, escFinal')
  where
    escFinal' = if escapes escTypeCaseBinder then Set.insert b escFinal else escFinal
    escFinal = escScrutFinal `Set.union` escAltsFinal
    (escScrut, escScrutFinal) = escapees (env `delEscapeEnv` b) scrut
    unionEscAlts = foldl unionEscapees emptyEscapees (map (\ (esc, _, _) -> esc) escapeesAlts)
    escapeesAlts = map escapeesAlt alts
      where
        escapeesAlt Alt {altBinders=binders, altRHS=expr} = (esc', escAltFinal, escType binders)
          where
            esc' = esc `delEscapees` binders
            (esc, escAltFinal) = escapees (env `delEscapeEnvList` binders) expr
            escType = foldl lubEscapeType Referred . mapMaybe (lookupEscapee esc)

    escAltsFinal = (foldl Set.union Set.empty . map (\ (_, esc, _) -> esc)) escapeesAlts

    escTypeCaseBinder = fromMaybe Referred (unionEscAlts `lookupEscapee` b)
    escTypeAltConBinders = foldl lubEscapeType Referred (map (\ (_, _, t) -> t) escapeesAlts)

escapees _ (StgApp var [] _ _) = (Map.singleton var Escaping, Set.empty)

escapees env (StgApp func args (SingleValue primRep) _)
  | isUnboxed primRep = (fmap (alterEscapeType Referred) (escapeesFunc env func args), Set.empty)

escapees env (StgApp func args (UnboxedTuple primReps) _)
  | all isUnboxed primReps = (fmap (alterEscapeType Referred) (escapeesFunc env func args), Set.empty)

escapees env (StgApp func args _ _) = (escapeesFunc env func args, Set.empty)

escapees _ (StgConApp _ conArgs _) = (mkEscapees (zip (varsFromArgs conArgs) (repeat Escaping)), Set.empty)

escapees _ (StgOpApp op args _ _)
  | hasSideEffects op = (mkEscapees (zip (varsFromArgs args) (repeat SideEffect)), Set.empty)
  where
    hasSideEffects (StgPrimOp name)
      = Set.member (BS.unpack name) sideEffectOps
    hasSideEffects (StgPrimCallOp (PrimCall name UnitId { getUnitId = uid }))
      = Set.member (BS.unpack uid) sideEffectOps
    hasSideEffects _ = True

escapees _ (StgOpApp _ args (SingleValue primRep) _)
  | isUnboxed primRep = (mkEscapees (zip (varsFromArgs args) (repeat Referred)), Set.empty)

escapees _ (StgOpApp _ args (UnboxedTuple primReps) _)
  | all isUnboxed primReps = (mkEscapees (zip (varsFromArgs args) (repeat Referred)), Set.empty)

escapees _ (StgOpApp _ args _ _) = (mkEscapees (zip (varsFromArgs args) (repeat Escaping)), Set.empty)

escapees _ (StgLit _) = (emptyEscapees, Set.empty)

escapees env (StgTick _ expr) = escapees env expr

escapeesFunc :: EscapeEnv -> Binder -> [Arg] -> Escapees
escapeesFunc env func args = case lookupJoinPoint env func of
    Just inside -> mkEscapees (escapingArgs' inside)
    _ -> mkEscapees (escapingArgs' Set.empty)
  where
    escapingArgs' :: Set.Set Binder -> [(Binder, EscapeType)]
    escapingArgs' inside =
      case lookupSignature env func of
        Just (Signature sig) | length args >= length sig -> (func, ValueEscaping)
          : map bindingsInsideEscaping (filterVarArgs $ zip args sig)
          ++ filterVarArgs (drop (length sig) (zip args (repeat SideEffect)))
        Just NoneEscape -> (func, ValueEscaping)
          : map bindingsInsideEscaping (filterVarArgs (zip args (repeat Referred)))
        _ -> (func, Escaping) : filterVarArgs (zip args (repeat SideEffect))
      where
        bindingsInsideEscaping bt@(b, t)
          | b `Set.member` inside = (b, lubEscapeType t Escaping)
          | otherwise = bt
    filterVarArgs ((StgVarArg b, t):args') = (b, t) : filterVarArgs args'
    filterVarArgs (_:args') = filterVarArgs args'
    filterVarArgs [] = []

isUnboxed :: PrimRep -> Bool
isUnboxed LiftedRep = False
isUnboxed UnliftedRep = False
isUnboxed _ = True

escapeesLet :: EscapeEnv -> Binding -> Expr -> Bool -> (Escapees, Set.Set Binder)
escapeesLet env bind body lne = case bind of
    StgNonRec b _ ->
      let (esc', _, escFinal') = escapeesBinding emptyEscapees envInit bind body lne
      in (esc' `delEscapee` b, escFinal')
    StgRec bs ->
      let (esc', _, escFinal') = escapeesFix emptyEscapees envInit
      in (esc' `delEscapees` map fst bs, escFinal')
  where
    escapeesFix :: Escapees -> EscapeEnv -> (Escapees, EscapeEnv, Set.Set Binder)
    escapeesFix escTmp envTmp
      | envTmp' == envTmp && escTmp' == escTmp = result
      | otherwise = escapeesFix escTmp' envTmp'
      where
        result@(escTmp', envTmp', _) = escapeesBinding escTmp envTmp bind body lne
    envInit = env `extendEnvBindInit` bind

extendEnvBindInit :: EscapeEnv -> Binding -> EscapeEnv
extendEnvBindInit env (StgNonRec b _) = extendEscapeEnv env b NoneEscape
extendEnvBindInit env (StgRec bs) = foldl extendEnvBindInit' env bs
  where
    extendEnvBindInit' env' (b, _) = extendEscapeEnv env' b NoneEscape

escapeesBinding :: Escapees -> EscapeEnv -> Binding -> Expr -> Bool -> (Escapees, EscapeEnv, Set.Set Binder)
escapeesBinding esc env bind body lne = case bind of
  StgNonRec b rhs ->
    let (esc', envFinal, escFinal) = escapeesBinding' env [(b, rhs)]
    in (esc', envFinal, if (escapes . fromMaybe Referred . lookupEscapee esc') b then b `Set.insert` escFinal else escFinal)
  StgRec bs ->
    let (esc', envFinal, escFinal) = escapeesBinding' env bs
    in (esc', envFinal, escFinal `Set.union` (Set.fromList . filter (escapes . fromMaybe Referred . lookupEscapee esc') . map fst) bs)
  where
    escapeesBinding' env' ((b, rhs):bs) = (esc', envFinal, escFinal)
      where
        envWithLne = if lne then addLneEscapeEnv env' b else env'
        esc' = case escType of
          Just t -> mergeEscapees t escTail escRhs
          Nothing -> escTail

        (sig, escRhs, escFinalRhs) = escapeesRhs envWithLne rhs
        (escTail, envFinal, escFinalTail) = escapeesBinding' (extendEscapeEnv envWithLne b sig) bs
        escFinal = escFinalRhs `Set.union` escFinalTail
        escType = lookupEscapee escTail b

    escapeesBinding' envFinal [] = (escBody `unionEscapees` esc, envFinal, escFinal)
      where
        (escBody, escFinal) = escapees envFinal body

escapeesRhs :: EscapeEnv -> Rhs -> (Signature, Escapees, Set.Set Binder)
escapeesRhs env (StgRhsClosure _ _ lamArgs lamBody) = (sig, escLam `delEscapees` lamArgs, escLamFinal)
  where
    sig = Signature (map (fromMaybe Referred . lookupEscapee escLam) lamArgs)
    (escLam, escLamFinal) = escapees (env `delEscapeEnvList` lamArgs) lamBody

escapeesRhs _ (StgRhsCon _ conArgs) = (NoneEscape, mkEscapees (zip vars (repeat Escaping)), Set.empty)
  where
    vars = varsFromArgs conArgs

sideEffectOps = Set.fromList [
      "newArray#"
    --, "readArray#"
    , "writeArray#"
    , "unsafeFreezeArray#"
    --, "unsafeThawArray#"
    , "copyArray#"
    , "copyMutableArray#"
    , "cloneArray#"
    , "cloneMutableArray#"
    --, "freezeArray#"
    --, "thawArray#"
    , "casArray#"
    , "newSmallArray#"
    --, "shrinkSmallMutableArray#"
    --, "readSmallArray#"
    , "writeSmallArray#"
    --, "unsafeFreezeSmallArray#"
    --, "unsafeThawSmallArray#"
    , "copySmallArray#"
    , "copySmallMutableArray#"
    , "cloneSmallArray#"
    , "cloneSmallMutableArray#"
    --, "freezeSmallArray#"
    --, "thawSmallArray#"
    , "casSmallArray#"
    , "newByteArray#"
    , "newPinnedByteArray#"
    , "newAlignedPinnedByteArray#"
    --, "shrinkMutableByteArray#"
    --, "resizeMutableByteArray#"
    --, "unsafeFreezeByteArray#"
    --, "readCharArray#"
    --, "readWideCharArray#"
    --, "readIntArray#"
    --, "readWordArray#"
    --, "readAddrArray#"
    --, "readFloatArray#"
    --, "readDoubleArray#"
    --, "readStablePtrArray#"
    --, "readInt8Array#"
    --, "readInt16Array#"
    --, "readInt32Array#"
    --, "readInt64Array#"
    --, "readWord8Array#"
    --, "readWord16Array#"
    --, "readWord32Array#"
    --, "readWord64Array#"
    --, "readWord8ArrayAsChar#"
    --, "readWord8ArrayAsWideChar#"
    --, "readWord8ArrayAsAddr#"
    --, "readWord8ArrayAsFloat#"
    --, "readWord8ArrayAsDouble#"
    --, "readWord8ArrayAsStablePtr#"
    --, "readWord8ArrayAsInt16#"
    --, "readWord8ArrayAsInt32#"
    --, "readWord8ArrayAsInt64#"
    --, "readWord8ArrayAsInt#"
    --, "readWord8ArrayAsWord16#"
    --, "readWord8ArrayAsWord32#"
    --, "readWord8ArrayAsWord64#"
    --, "readWord8ArrayAsWord#"
    , "writeCharArray#"
    , "writeWideCharArray#"
    , "writeIntArray#"
    , "writeWordArray#"
    , "writeAddrArray#"
    , "writeFloatArray#"
    , "writeDoubleArray#"
    , "writeStablePtrArray#"
    , "writeInt8Array#"
    , "writeInt16Array#"
    , "writeInt32Array#"
    , "writeInt64Array#"
    , "writeWord8Array#"
    , "writeWord16Array#"
    , "writeWord32Array#"
    , "writeWord64Array#"
    , "writeWord8ArrayAsChar#"
    , "writeWord8ArrayAsWideChar#"
    , "writeWord8ArrayAsAddr#"
    , "writeWord8ArrayAsFloat#"
    , "writeWord8ArrayAsDouble#"
    , "writeWord8ArrayAsStablePtr#"
    , "writeWord8ArrayAsInt16#"
    , "writeWord8ArrayAsInt32#"
    , "writeWord8ArrayAsInt64#"
    , "writeWord8ArrayAsInt#"
    , "writeWord8ArrayAsWord16#"
    , "writeWord8ArrayAsWord32#"
    , "writeWord8ArrayAsWord64#"
    , "writeWord8ArrayAsWord#"
    , "copyByteArray#"
    , "copyMutableByteArray#"
    , "copyByteArrayToAddr#"
    , "copyMutableByteArrayToAddr#"
    , "copyAddrToByteArray#"
    , "setByteArray#"
    --, "atomicReadIntArray#"
    , "atomicWriteIntArray#"
    , "casIntArray#"
    , "fetchAddIntArray#"
    , "fetchSubIntArray#"
    , "fetchAndIntArray#"
    , "fetchNandIntArray#"
    , "fetchOrIntArray#"
    , "fetchXorIntArray#"
    , "newArrayArray#"
    --, "unsafeFreezeArrayArray#"
    --, "readByteArrayArray#"
    --, "readMutableByteArrayArray#"
    --, "readArrayArrayArray#"
    --, "readMutableArrayArrayArray#"
    , "writeByteArrayArray#"
    , "writeMutableByteArrayArray#"
    , "writeArrayArrayArray#"
    , "writeMutableArrayArrayArray#"
    , "copyArrayArray#"
    , "copyMutableArrayArray#"
    --, "readCharOffAddr#"
    --, "readWideCharOffAddr#"
    --, "readIntOffAddr#"
    --, "readWordOffAddr#"
    --, "readAddrOffAddr#"
    --, "readFloatOffAddr#"
    --, "readDoubleOffAddr#"
    --, "readStablePtrOffAddr#"
    --, "readInt8OffAddr#"
    --, "readInt16OffAddr#"
    --, "readInt32OffAddr#"
    --, "readInt64OffAddr#"
    --, "readWord8OffAddr#"
    --, "readWord16OffAddr#"
    --, "readWord32OffAddr#"
    --, "readWord64OffAddr#"
    , "writeCharOffAddr#"
    , "writeWideCharOffAddr#"
    , "writeIntOffAddr#"
    , "writeWordOffAddr#"
    , "writeAddrOffAddr#"
    , "writeFloatOffAddr#"
    , "writeDoubleOffAddr#"
    , "writeStablePtrOffAddr#"
    , "writeInt8OffAddr#"
    , "writeInt16OffAddr#"
    , "writeInt32OffAddr#"
    , "writeInt64OffAddr#"
    , "writeWord8OffAddr#"
    , "writeWord16OffAddr#"
    , "writeWord32OffAddr#"
    , "writeWord64OffAddr#"
    , "newMutVar#"
    --, "readMutVar#"
    , "writeMutVar#"
    , "atomicModifyMutVar2#"
    , "atomicModifyMutVar_#"
    , "casMutVar#"
    , "catch#"
    , "raise#"
    , "raiseDivZero#"
    , "raiseUnderflow#"
    , "raiseOverflow#"
    , "raiseIO#"
    , "maskAsyncExceptions#"
    , "maskUninterruptible#"
    , "unmaskAsyncExceptions#"
    , "getMaskingState#"
    , "atomically#"
    , "retry#"
    , "catchRetry#"
    , "catchSTM#"
    , "newTVar#"
    --, "readTVar#"
    --, "readTVarIO#"
    , "writeTVar#"
    , "newMVar#"
    --, "takeMVar#"
    --, "tryTakeMVar#"
    , "putMVar#"
    , "tryPutMVar#"
    --, "readMVar#"
    --, "tryReadMVar#"
    --, "isEmptyMVar#"
    --, "delay#"
    --, "waitRead#"
    --, "waitWrite#"
    , "fork#"
    , "forkOn#"
    --, "killThread#"
    --, "yield#"
    --, "myThreadId#"
    , "labelThread#"
    --, "isCurrentThreadBound#"
    --, "noDuplicate#"
    --, "threadStatus#"
    , "mkWeak#"
    , "mkWeakNoFinalizer#"
    , "addCFinalizerToWeak#"
    --, "deRefWeak#"
    --, "finalizeWeak#"
    --, "touch#"
    , "makeStablePtr#"
    --, "deRefStablePtr#"
    --, "eqStablePtr#"
    , "makeStableName#"
    , "compactNew#"
    --, "compactResize#"
    --, "compactAllocateBlock#"
    --, "compactFixupPointers#"
    , "compactAdd#"
    , "compactAddWithSharing#"
    --, "compactSize#"
    --, "par#"
    --, "spark#"
    --, "getSpark#"
    --, "numSparks#"
    , "newBCO#"
    , "traceEvent#"
    , "traceBinaryEvent#"
    , "traceMarker#"
    , "setThreadAllocationCounter#"
    --, "readArray#"
    , "writeArray#"
    --, "readOffAddr#"
    , "writeOffAddr#"
    --, "readArrayAs#"
    , "writeArrayAs#"
    --, "readOffAddrAs#"
    , "writeOffAddrAs#"
    --, "prefetchByteArray3#"
    --, "prefetchMutableByteArray3#"
    --, "prefetchAddr3#"
    --, "prefetchValue3#"
    --, "prefetchByteArray2#"
    --, "prefetchMutableByteArray2#"
    --, "prefetchAddr2#"
    --, "prefetchValue2#"
    --, "prefetchByteArray1#"
    --, "prefetchMutableByteArray1#"
    --, "prefetchAddr1#"
    --, "prefetchValue1#"
    --, "prefetchByteArray0#"
    --, "prefetchMutableByteArray0#"
    --, "prefetchAddr0#"
    --, "prefetchValue0#"
  ]