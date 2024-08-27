import itertools
import os
import random

def escalating(choice):
    x = 0
    y = 0
    while True:
        yield (x, y)
        if x % 2 == 0:
            y += 1
        else:
            y += x
        inc = choice(x, y)
        assert inc in (1, 2)
        x += inc

def max_diff_max_value(init):
    max = init
    while True:
        yield max
        max += 1

def max_strat(x, y):
    if x == 0:
        return 1
    else:
        return 2

def min_strat(x, y):
    return 2

def random_strat(x, y):
    return random.getrandbits(1) + 1

def for_n(n, init_max):
    def cutoff(g):
        return list(itertools.islice(g, n))

    max_diffs = cutoff(max_diff_max_value(init_max))
    max_strat_observations = cutoff(escalating(max_strat))
    min_strat_observations = cutoff(escalating(min_strat))

    max_x = min_strat_observations[n - 1][0]
    assert max_x == 2 * (n - 1)
    max_y = max_strat_observations[n - 1][1]
    max_max = max_diffs[n - 1]

    # Sanity check.
    for _ in range(1000):
        for idx, point in enumerate(cutoff(escalating(random_strat))):
            assert point[0] <= 2 * idx
            assert point[1] <= max_strat_observations[idx][1]
            assert point[1] >= min_strat_observations[idx][1]
            assert point[0] <= max_x
            assert point[1] <= max_y

    violation = None

    for idx in range(n):
        if max_strat_observations[idx][1] > max_diffs[idx]:
            violation = (idx, max_strat_observations[idx])
            break

    return ({
        'x': max_x,
        'y': max_y,
        'max': max_max,
    }, violation)

dirpath = os.path.dirname(__file__)
templates_dir = os.path.join(dirpath, 'templates')
output_dir = os.path.join(dirpath, 'generated')
os.mkdir(output_dir)

def instantiate_templates(n_min_obs, init_max, domain_limits):
    replacements = {
        'N_MIN_OBS': n_min_obs,
        'MAX_VALUE_OF_X': domain_limits['x'],
        'MAX_VALUE_OF_X_PLUS_1': domain_limits['x'] + 1,
        'MAX_VALUE_OF_Y': domain_limits['y'],
        'MAX_VALUE_OF_Y_PLUS_1': domain_limits['y'] + 1,
        'MAX_VALUE_OF_MAX': domain_limits['max'],
        'MAX_VALUE_OF_MAX_PLUS_1': domain_limits['max'] + 1,
        'INITIAL_VALUE_OF_MAX': init_max,
    }
    for filename in os.listdir(templates_dir):
        template_path = os.path.join(templates_dir, filename)
        with open(template_path, 'r') as f:
            template_str = f.read()
        for key, value in replacements.items():
            template_str = template_str.replace(f'{{{{{key}}}}}', str(value))
        new_filename = f'p{init_max:02d}_' + filename.replace('.template', '')
        output_path = os.path.join(output_dir, new_filename)
        with open(output_path, 'w') as f:
            f.write(template_str)

next_init_max = 0
for n in range(1, 11):
    last_violation = None
    for init_max in itertools.count():
        domain_limits, violation = for_n(n, init_max)
        if violation is None:
            break
        else:
            last_violation = violation
    if last_violation is None:
        print(f'n = {n}: no initial value for max results in a counterexample within {n} observations')
    else:
        assert last_violation[0] == n - 1
        print(f'n = {n}:\tthe initial value for a counterexample within {n} observations must be strictly less than {init_max}')
        for i in range(next_init_max, init_max):
            domain_limits, violation = for_n(n, i)
            print(f'\t\tlimits for init_max = {i}: {domain_limits}')
            instantiate_templates(n, i, domain_limits)
        next_init_max = init_max
