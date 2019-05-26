import re

PWD_PATTERN = re.compile(r'\(\*\*PWD\*\* (?P<pwd>.*?) \*\*\)')

ML_PATHS_PATTERN = re.compile(r'\(\*\*ML_PATH\*\* (?P<ml_paths>.*?) \*\*\)', flags=re.DOTALL)

ML_PATH_PATTERN = re.compile(r'(\/[0-9A-Za-z_-]+)+')

LOAD_PATHS_PATTERN = re.compile(r'\(\*\*LOAD_PATH\*\* (?P<load_paths>.*?) \*\*\)', flags=re.DOTALL)

LOAD_PATH_PATTERN = re.compile(r'(?P<logical_path><>|([0-9A-Za-z_-]+(\.[0-9A-Za-z_-]+)*))\s+(?P<physical_path>(\/[0-9A-Za-z_-]+)+)\s+(?P<implicit>true|false)', re.DOTALL)

LOC_PATTERN = re.compile(r'\(\*\*LOC\*\* .+?(?=$|\(\*\*LOC)', flags=re.DOTALL)

PARSE_LOC_PATTERN = re.compile(r'Loc.bp = (?P<bp>\d+); Loc.ep = (?P<ep>\d+)')

TAG_PATTERN = re.compile(r'\(\*\*(?P<tag>[A-Z_]+)(\*\*)?(?P<content>.*?)\*\*\)')

UNBOUND_REL_PATTERN = re.compile(r'_UNBOUND_REL_\d+')

ADDED_STATE_PATTERN = re.compile(r'\(Added (?P<state_id>\d+)')

TYPE_PATTERN = re.compile(r'\(Pp_tag constr.type\(Pp_string (?P<type>"(?:\\"|[^"])*?"|[^\(\)\s"]*)\)\)')
