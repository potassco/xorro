#!/usr/bin/env python

from setuptools import setup

setup(
    version = '1.0',
    name = 'xorro',
    description = 'Extending ASP with parity constraints.',
    author = 'Flavio Everardo',
    license = 'MIT',
    packages = ['xorro'],
    test_suite = 'xorro.tests',
    zip_safe = False,
    entry_points = {
        'console_scripts': [
            'xorro = xorro:main',
        ]
    }
)

