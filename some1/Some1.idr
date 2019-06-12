-- https://reasonablypolymorphic.com/some1-like-you/#/title

data Value
  = VObject (List (String, Value))
  | VArray (List Value)
  | VString String
  | VNumber Double
  | VBool Bool
  | VNull

interface FromJSON a where
  fromJSON : Value -> Maybe a

interface ToJSON a where
  toJSON : a -> Value

data Meal = MkMeal
data Song = MkSong
data Duration = MkDuration

data PayloadWakeUp = MkPayloadWakeUp

implementation ToJSON PayloadWakeUp where
  toJSON _ = VNull

implementation FromJSON PayloadWakeUp where
  fromJSON _ = Nothing

data PayloadEat = MkPayloadEat Meal

implementation ToJSON PayloadEat where
  toJSON _ = VNull

implementation FromJSON PayloadEat where
  fromJSON _ = Nothing

data PayloadRockOut = MkPayloadRockOut Song Duration

implementation ToJSON PayloadRockOut where
  toJSON _ = VNull

implementation FromJSON PayloadRockOut where
  fromJSON _ = Nothing

data EventType = WakeUp | Eat | RockOut

implementation ToJSON EventType where
  toJSON WakeUp = VString "WakeUp"
  toJSON Eat = VString "Eat"
  toJSON RockOut = VString "RockOut"

implementation FromJSON EventType where
  fromJSON (VString "WakeUp") = Just WakeUp
  fromJSON (VString "Eat") = Just Eat
  fromJSON (VString "RockOut") = Just RockOut
  fromJSON _ = Nothing

namespace Payload
  Payload : EventType -> Type
  Payload WakeUp = PayloadWakeUp
  Payload Eat = PayloadEat
  Payload RockOut = PayloadRockOut

  fromJSON : (et : EventType) -> Value -> (Maybe (Payload et))
  fromJSON WakeUp v = the (Maybe (Payload WakeUp)) (fromJSON v)
  fromJSON Eat v = the (Maybe (Payload Eat)) (fromJSON v)
  fromJSON RockOut v = the (Maybe (Payload RockOut)) (fromJSON v)

  toJSON : (et : EventType) -> Payload et -> Value
  toJSON WakeUp payload = toJSON (the (Payload WakeUp) payload)
  toJSON Eat payload = toJSON (the (Payload Eat) payload)
  toJSON RockOut payload = toJSON (the (Payload RockOut) payload)

data Event : Type where
  MkEvent : (et : EventType) -> Payload et -> Event

implementation ToJSON Event where
  toJSON (MkEvent et payload) =
    VObject [("type", toJSON et), ("payload", toJSON et payload)]

implementation FromJSON Event where
  fromJSON (VObject [("type", vet), ("payload", vpayload)]) =
    case the (Maybe EventType) (fromJSON vet) of
      Nothing => Nothing
      Just et => case fromJSON et vpayload of
        Nothing => Nothing
        Just payload => Just (MkEvent et payload)
  fromJSON _ = Nothing
