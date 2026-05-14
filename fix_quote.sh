#!/bin/bash

# This script adds db parameter to all quote functions systematically

FILE="crates/hwml-core/src/quote.rs"

# Backup
cp "$FILE" "$FILE.bak"

# Add db parameter to function signatures that start with "pub fn quote"
# Pattern: global: &GlobalEnv<'db>, -> db: &'db dyn salsa::Database, global: &GlobalEnv<'db>,
sed -i '' 's/^\(pub fn quote[a-z_]*<'"'"'db>(\)$/\1/; /^pub fn quote[a-z_]*<'"'"'db>($/,/^) -> Result</ { s/^    global: \&GlobalEnv<'"'"'db>,$/    db: \&'"'"'db dyn salsa::Database,\n    global: \&GlobalEnv<'"'"'db>,/; }' "$FILE"

# Now update all internal calls
# Pattern: quote_xyz(global, -> quote_xyz(db, global,
sed -i '' 's/quote_\([a-z_]*\)(global,/quote_\1(db, global,/g' "$FILE"
sed -i '' 's/quote(global,/quote(db, global,/g' "$FILE"
sed -i '' 's/type_quote(global,/type_quote(db, global,/g' "$FILE"

echo "Done! Check $FILE for correctness"
echo "Backup saved to $FILE.bak"
