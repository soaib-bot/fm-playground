logics_contains = {
    "QF_AX": [],
    "QF_IDL": ["QF_LIA", "QF_UFIDL"],
    "QF_UF": ["QF_UFIDL", "QF_UFLRA", "QF_UFBV"],
    "QF_BV": ["QF_UFBV", "QF_ABV"],
    "QF_RDL": ["QF_LRA", "QF_UFLRA"],
    "QF_LIA": ["QF_NIA", "LIA", "QF_ALIA", "QF_UFLIA"],
    "QF_UFIDL": ["QF_UFLIA"],
    "QF_UFBV": ["QF_AUFBV"],
    "QF_ABV": ["QF_AUFBV"],
    "QF_LRA": ["QF_UFNRA", "LRA", "QF_NRA"],
    "QF_NIA": ["NIA"],
    "LIA": ["NIA", "AUFLIRA", "ALIA"],
    "QF_ALIA": ["ALIA", "QF_AUFLIA"],
    "QF_UFLIA": ["QF_AUFLIA", "QF_UFNIA"],
    "QF_UFLRA": ["UFLRA", "QF_UFNRA"],
    "QF_AUFBV": [],
    "LRA": ["UFLERA", "NRA"],
    "QF_NRA": ["NRA"],
    "NIA": ["UFNIA"],
    "ALIA": ["AUFLIA"],
    "QF_AUFLIA": ["AUFLIA"],
    "QF_UFNIA": ["UFNIA"],
    "UFLRA": ["AUFLIRA"],
    "QF_UFNRA": ["AUFNIRA"],
    "NRA": ["AUFNIRA"],
    "UFNIA": ["AUFNIRA"],
    "AUFLIA": [],
    "AUFLIRA": ["AUFNIRA"],
    "AUFNIRA": [],
}

z3_contains = {
    "QF_UF": ["QF_UFBV"],
    "QF_BV": ["QF_UFBV", "QF_ABV"],
    "QF_IDL": ["QF_LIA"],
    "QF_LIA": ["QF_NIA", "LIA"],
    "QF_LRA": ["LRA", "QF_NRA"],
    "QF_NIA": [],
    "QF_NRA": ["NRA"],
    "QF_AUFLIA": ["AUFLIA"],
    "QF_AUFBV": [],
    "QF_ABV": ["QF_AUFBV"],
    "QF_UFBV": ["QF_AUFBV"],
    "AUFLIA": [],
    "AUFLIRA": ["AUFNIRA"],
    "AUFNIRA": [],
    "UFNIA": ["AUFNIRA"],
    "UFLRA": ["AUFLIRA"],
    "LRA": ["NRA"],
    "NRA": ["AUFNIRA"],
    "LIA": ["AUFLIRA"],
    "UFBV": [],
    "BV": [],
    "QF_FP": [],
    "QF_FPBV": [],
    "QF_BVFP": [],
    "HORN": [],
    "QF_FD": [],
    "SAT": [],
}

Z3_SUPPORTED_LOGICS = [
    "QF_UF",
    "QF_BV",
    "QF_IDL",
    "QF_LIA",
    "QF_LRA",
    "QF_NIA",
    "QF_NRA",
    "QF_AUFLIA",
    "QF_AUFBV",
    "QF_ABV",
    "QF_UFBV",
    "AUFLIA",
    "AUFLIRA",
    "AUFNIRA",
    "UFNIA",
    "UFLRA",
    "LRA",
    "NRA",
    "LIA",
    "UFBV",
    "BV",
    "QF_FP",
    "QF_FPBV",
    "QF_BVFP",
    "HORN",
    "QF_FD",
    "SAT",
]


def get_supersets(logic, contains):
    supersets = set()
    stack = [logic]
    while stack:
        current = stack.pop()
        for sup in contains.get(current, []):
            if sup not in supersets:
                supersets.add(sup)
                stack.append(sup)
    return supersets


def common_logic(logic1, logic2, contains=z3_contains):
    # include the logics themselves
    anc1 = get_supersets(logic1, contains) | {logic1}
    anc2 = get_supersets(logic2, contains) | {logic2}
    common = anc1 & anc2
    if not common:
        return None  # no overlap

    # pick the most specific one (not contained in any other in 'common')
    def is_most_specific(l):
        return not any(
            l in get_supersets(other, contains) for other in common if other != l
        )

    return [l for l in common if is_most_specific(l)][0]
