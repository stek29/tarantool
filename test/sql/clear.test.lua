test_run = require('test_run').new()
engine = test_run:get_cfg('engine')
box.sql.execute('pragma sql_default_engine=\''..engine..'\'')

-- box.cfg()

-- create space
box.sql.execute("CREATE TABLE zoobar (c1 INT, c2 INT PRIMARY KEY, c3 TEXT, c4 INT)")
box.sql.execute("CREATE UNIQUE INDEX zoobar2 ON zoobar(c1, c4)")

-- Debug
-- box.sql.execute("PRAGMA vdbe_debug=ON;")

-- Seed entry
for i=1, 100 do box.sql.execute(string.format("INSERT INTO zoobar VALUES (%d, %d, 'c3', 444)", i+i, i)) end

-- Check table is not empty
box.sql.execute("SELECT * FROM zoobar")

-- Do clean up
box.sql.execute("DELETE FROM zoobar")

-- Make sure table is empty
box.sql.execute("SELECT * from zoobar")

-- Cleanup
box.sql.execute("DROP INDEX zoobar2 ON zoobar")
box.sql.execute("DROP TABLE zoobar")

-- Debug
-- require("console").start()
