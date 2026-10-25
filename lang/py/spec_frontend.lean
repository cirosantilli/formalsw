import lang.py.SpecFrontend

/-! Keep the executable wrapper small: Lake compiles the parser once. -/

unsafe def main : IO Unit := FormalSW.SpecFrontend.run
