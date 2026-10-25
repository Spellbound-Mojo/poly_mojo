# expect: expression must be mutable in assignment
from poly import sparse


def main() raises:
    var result = sparse.gcd_checked([((1, 0), 1)], [((0, 1), 1)])
    result.evidence().coprimality.value().modular.value().prime = 4
