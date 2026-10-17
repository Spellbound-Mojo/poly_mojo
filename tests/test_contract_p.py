"""Check the frozen Contract P declarations without changing the build tooling.

Run from the repository root: pixi run python tests/test_contract_p.py
The snapshot is reviewed release data; this test has no update mode.
"""
import ast
import copy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from mojo_api import parse  # noqa: E402

SNAPSHOT = ROOT / "docs/content/reference/contract-p.json"
REVISION_ONE = ROOT / "docs/content/reference/contract-p-v1.json"
NUMERICAL = ROOT / "docs/content/reference/contract-numeric.json"
FINAL_REVISION_TWO = ROOT / "docs/content/reference/contract-p-v2.json"
INITIAL_REVISION_TWO = ROOT / "docs/content/reference/contract-p-v2-initial.json"
REVISION_THREE = ROOT / "docs/content/reference/contract-p-v3.json"


def declaration(item):
    return {
        "name": item.name,
        "signature": item.signature,
        "members": [declaration(member) for member in item.members],
    }


def current_contract(*, include_numerical=False):
    exports = []
    numerical_names = {item["name"] for item in json.loads(NUMERICAL.read_text())["exports"]}
    tree = ast.parse((ROOT / "src/polynomials/__init__.mojo").read_text())
    modules = {}
    for node in tree.body:
        if not isinstance(node, ast.ImportFrom):
            continue
        if node.level != 1 or any(alias.asname for alias in node.names):
            raise ValueError("review new root export syntax before changing Contract P")
        path = ROOT / f"src/polynomials/{node.module}.mojo"
        if node.module not in modules:
            modules[node.module] = {item.name: item for item in parse(path)[1]}
        for alias in node.names:
            if not include_numerical and alias.name in numerical_names:
                continue
            exports.append({
                "module": node.module,
                **declaration(modules[node.module][alias.name]),
            })
    return {"contract": "P", "revision": 4, "exports": sorted(exports, key=lambda x: x["name"])}


def migrated_declaration(item, *, storage=True):
    """Allow only the reviewed changes in older snapshots: the revision-3 dense
    storage change (when `storage`) and the revision-4 `certify` option."""
    item = copy.deepcopy(item)
    if item["name"] == "groebner":
        old = "track_cofactors: Bool = False) raises"
        assert old in item["signature"]
        item["signature"] = item["signature"].replace(old, "track_cofactors: Bool = False, certify: Bool = True) raises")
    if storage and item["name"] == "DensePoly":
        members = item["members"]
        field = next(member for member in members if member["name"] == "coefficients")
        assert field["signature"] == "var coefficients: List[Self.C]"
        field["signature"] = "var coefficients: CoefficientBuffer[Self.C]"
        factory = next(i for i, member in enumerate(members) if member["name"] == "from_coefficients")
        added = copy.deepcopy(members[factory])
        added["signature"] = added["signature"].replace("List[Self.C]", "CoefficientBuffer[Self.C]")
        members.insert(factory + 1, added)
    return item


class ContractP(unittest.TestCase):
    def test_public_declarations_are_frozen(self):
        expected = json.loads(SNAPSHOT.read_text())
        self.maxDiff = None
        self.assertEqual(current_contract(), expected,
                         "Contract P changed: agree the change and migration with consumers first")

    def test_numerical_declarations_are_separately_frozen(self):
        expected = json.loads(NUMERICAL.read_text())
        names = {item["name"] for item in expected["exports"]}
        actual = [item for item in current_contract(include_numerical=True)["exports"]
                  if item["name"] in names]
        self.assertEqual(actual, expected["exports"])
        self.assertTrue(names.isdisjoint(item["name"] for item in json.loads(SNAPSHOT.read_text())["exports"]))

    def test_final_revision_two_has_only_reviewed_storage_change(self):
        baseline = json.loads(FINAL_REVISION_TWO.read_text())
        current = {item["name"]: item for item in current_contract()["exports"]}
        for item in baseline["exports"]:
            with self.subTest(name=item["name"]):
                self.assertEqual(migrated_declaration(item), current[item["name"]])

    def test_exports_are_unique(self):
        names = [item["name"] for item in current_contract(include_numerical=True)["exports"]]
        self.assertEqual(len(names), len(set(names)))

    def test_revision_one_has_only_reviewed_storage_change(self):
        baseline = json.loads(REVISION_ONE.read_text())
        current = {item["name"]: item for item in current_contract()["exports"]}
        for item in baseline["exports"]:
            with self.subTest(name=item["name"]):
                self.assertIn(item["name"], current)
                self.assertEqual(migrated_declaration(item), current[item["name"]])

    def test_initial_revision_two_has_only_reviewed_storage_change(self):
        baseline = json.loads(INITIAL_REVISION_TWO.read_text())
        current = {item["name"]: item for item in current_contract()["exports"]}
        for item in baseline["exports"]:
            with self.subTest(name=item["name"]):
                self.assertIn(item["name"], current)
                self.assertEqual(migrated_declaration(item), current[item["name"]])

    def test_revision_three_has_only_reviewed_certify_option(self):
        baseline = json.loads(REVISION_THREE.read_text())
        current = {item["name"]: item for item in current_contract()["exports"]}
        for item in baseline["exports"]:
            with self.subTest(name=item["name"]):
                self.assertIn(item["name"], current)
                self.assertEqual(migrated_declaration(item, storage=False), current[item["name"]])


if __name__ == "__main__":
    unittest.main()
