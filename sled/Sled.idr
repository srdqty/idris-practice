data IField : Nat -> Nat -> Type where
  Opcode : IField 0 6
  Rd : IField 7 11
  Funct3 : IField 12 14
  Rs1 : IField 15 19
  Rs2 : IField 20 24
  Funct7 : IField 25 31
  ImmI11_0 : IField 20 31
  ImmS4_0 : IField 7 11
  ImmS115 : IField 25 31
  ImmB11 : IField 7 7
  ImmB41 : IField 8 11
  ImmB105 : IField 25 30
  ImmB12 : IField 31 31
  ImmU3112 : IField 12 31
  ImmJ1912 : IField 12 19
  ImmJ11 : IField 20 20
  ImmJ101 : IField 31 30
  ImmJ20 : IField 31 31

data Token : String -> Nat -> (Nat -> Nat -> Type) -> Type where
  MkToken : (name : String)
         -> (width : Nat)
         -> (fields : Nat -> Nat -> Type)
         -> Token name width fields

IToken : Type
IToken = Token "Instruction Token" 32 IField

data Pattern : (fieldTy : Nat -> Nat -> Type) -> Type where
  And : Pattern fieldTy -> Pattern fieldTy -> Pattern fieldTy
  Or : Pattern fieldTy -> Pattern fieldTy -> Pattern fieldTy
  Sequence : Pattern fieldTy -> Pattern fieldTy -> Pattern fieldTy
  -- Flesh out the constraint expressions
  Constraint : (field : fieldTy i j) -> Pattern fieldTy
