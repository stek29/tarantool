test_run = require('test_run').new()
engine = test_run:get_cfg('engine')
box.sql.execute('pragma sql_default_engine=\''..engine..'\'')

-- box.cfg()

-- create space
box.sql.execute("CREATE TABLE zzzoobar (c1, c2 PRIMARY KEY, c3, c4)")

-- Debug
-- box.sql.execute("PRAGMA vdbe_debug=ON ; INSERT INTO zzzoobar VALUES (111, 222, 'c3', 444)")

box.sql.execute("CREATE INDEX zb ON zzzoobar(c1, c3)")

-- Dummy entry
box.sql.execute("INSERT INTO zzzoobar VALUES (111, 222, 'c3', 444)")

box.sql.execute("DROP TABLE zzzoobar")

-- Table does not exist anymore. Should error here.
box.sql.execute("INSERT INTO zzzoobar VALUES (111, 222, 'c3', 444)")

-- gh-3712: if space features sequence, data from _sequence_data
-- must be deleted before space is dropped.
--
box.sql.execute("CREATE TABLE t1 (id INT PRIMARY KEY AUTOINCREMENT);")
box.sql.execute("INSERT INTO t1 VALUES (NULL);")
box.snapshot()
test_run:cmd('restart server default')
box.sql.execute("DROP TABLE t1;")

-- Cleanup
-- DROP TABLE should do the job

-- Debug
-- require("console").start()
