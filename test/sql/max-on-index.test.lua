test_run = require('test_run').new()
engine = test_run:get_cfg('engine')
box.sql.execute('pragma sql_default_engine=\''..engine..'\'')

-- box.cfg()

-- create space
-- scalar affinity
box.sql.execute("CREATE TABLE test1 (f1 INT, f2 INT, PRIMARY KEY(f1))")
box.sql.execute("CREATE INDEX test1_index ON test1 (f2)")

-- integer affinity
box.sql.execute("CREATE TABLE test2 (f1 INT, f2 INT, PRIMARY KEY(f1))")

-- Debug
-- box.sql.execute("PRAGMA vdbe_debug=ON ; INSERT INTO zoobar VALUES (111, 222, 'c3', 444)")

-- Seed entries
box.sql.execute("INSERT INTO test1 VALUES(1, 2)");
box.sql.execute("INSERT INTO test1 VALUES(2, NULL)");
box.sql.execute("INSERT INTO test1 VALUES(3, NULL)");
box.sql.execute("INSERT INTO test1 VALUES(4, 3)");

box.sql.execute("INSERT INTO test2 VALUES(1, 2)");

-- Select must return properly decoded `NULL`
box.sql.execute("SELECT MAX(f1) FROM test1")
box.sql.execute("SELECT MAX(f2) FROM test1")

box.sql.execute("SELECT MAX(f1) FROM test2")

-- Cleanup
box.sql.execute("DROP INDEX test1_index ON test1")
box.sql.execute("DROP TABLE test1")
box.sql.execute("DROP TABLE test2")

-- Debug
-- require("console").start()
