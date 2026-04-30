#!/bin/bash

sed -i '1s/^/{-# OPTIONS -Wno-unused-matches #-}\n/' src/Tog/Raw/Layout.hs
sed -i '1s/^/{-# OPTIONS -Wno-unused-local-binds #-}\n/' src/Tog/Raw/Layout.hs
sed -i '1s/^/{-# LANGUAGE NoPatternSynonyms #-}\n/' src/Tog/Raw/Print.hs
sed -i '1s/^/{-# LANGUAGE OverlappingInstances #-}\n/' src/Tog/Raw/Print.hs
sed -i '1s/^/{-# OPTIONS -Wwarn #-}\n/' src/Tog/Raw/Print.hs
sed -i '1s/^/{-# LANGUAGE NoPatternSynonyms #-}\n/' src/Tog/Raw/Skel.hs
sed -i '1s/^/{-# OPTIONS -Wno-unused-matches #-}\n/' src/Tog/Raw/Skel.hs
