"""Known-source controls for the source declaration reader."""
from lean_declarations import declarations
from principia_lean_interleave import ANCHOR_TO_ITEM, source_anchors

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

# Multiple modifiers must retain private visibility (prefixMax regression).
assert list(declarations("private noncomputable def hidden : Nat := 0"))[0][4]
assert not list(declarations("noncomputable def publicValue : Nat := 0"))[0][4]

# Editorial source placement reads comments, including refactored Latin markers,
# and does not mistake strings in Lean declarations for source citations.
anchors = source_anchors('''
/- LATIN BEGIN NATP00077.par44
LATIN END NATP00077.par44 -/
/-! 1713 NATP00082 par50; repeated NATP00077.par44 -/
def example := "NATP00077.par48"
''')
assert anchors == ['NATP00077.par44', 'NATP00082.par50']
assert ANCHOR_TO_ITEM[anchors[0]] == ANCHOR_TO_ITEM[anchors[1]]
