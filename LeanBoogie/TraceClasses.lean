import Lean

open Lean

initialize registerTraceClass `LeanBoogie.dsl
initialize registerTraceClass `LeanBoogie.normConTy

namespace LeanBoogie

def logger [Monad m] [MonadTrace m] [MonadLiftT IO m] [MonadRef m] [AddMessageContext m]
  [MonadOptions m] {α : Type} [MonadAlwaysExcept Exception m] [MonadLiftT BaseIO m] [ToMessageData α]
  (fn : MessageData)
  (ok : {_ : α} -> MessageData := @fun val => m!"{val}")
  (err : {_ : Exception} -> MessageData := @fun e => m!"💥️ {e.toMessageData}")
  : Except Exception α → m MessageData
| .ok val => return m!"{fn} ~~> {@ok val}"
| .error e => return m!"{fn} ~~> {@err e}"

def logger' [Monad m] [MonadTrace m] [MonadLiftT IO m] [MonadRef m] [AddMessageContext m]
  [MonadOptions m] {α : Type} [MonadAlwaysExcept Exception m] [MonadLiftT BaseIO m]
  (fn : MessageData)
  (ok : {_ : α} -> MessageData := "✓")
  (err : {_ : Exception} -> MessageData := @fun e => m!"💥️ {e.toMessageData}")
  : Except Exception α → m MessageData
| .ok val => return m!"{fn} ~~> {@ok val}"
| .error e => return m!"{fn} ~~> {@err e}"
