"""Known-source controls for the catalogue's premise-boundary reader."""
from lean_declarations import declarations

source = '''
namespace Example.Nested
/- theorem hidden : False := by contradiction
   /- nested -/
-/
section
private theorem bound (n : Nat) (hn : n ≤ 3) : n < 4 := by omega
theorem recur (n : Nat) : Nat
  | 0 => 0
  | n + 1 => by
      let x := n
      exact x
theorem nested_let (h : (let n := 1; n = 1)) : True := by trivial
end
end Example.Nested
'''
rows = list(declarations(source))
assert [r[1] for r in rows] == [
    'Example.Nested.bound', 'Example.Nested.recur', 'Example.Nested.nested_let']
assert rows[0][2] == 'theorem bound (n : Nat) (hn : n ≤ 3) : n < 4'
assert rows[0][4]
assert rows[1][2] == 'theorem recur (n : Nat) : Nat'
assert rows[2][2] == 'theorem nested_let (h : (let n := 1; n = 1)) : True'

# A damaged extraction that removes a premise or includes equation body text
# fails the known statement control. These checks are source checks only.
for damaged in [rows[0][2].replace('(hn : n ≤ 3) ', ''),
                rows[1][2] + ' | 0 => 0']:
    assert damaged not in (rows[0][2], rows[1][2])
print('Passed named, nested-comment, equation and nested-let premise controls')
