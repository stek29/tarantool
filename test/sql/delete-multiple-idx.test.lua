test_run = require('test_run').new()
engine = test_run:get_cfg('engine')
box.sql.execute('pragma sql_default_engine=\''..engine..'\'')

-- box.cfg()

-- Create space.
box.sql.execute("CREATE TABLE t3(id INT primary key,x INT,y INT);");
box.sql.execute("CREATE UNIQUE INDEX t3y ON t3(y);");

-- Debug.
-- box.sql.execute("PRAGMA vdbe_debug=ON ; INSERT INTO zoobar VALUES (111, 222, 'c3', 444)")

-- Seed entries.
box.sql.execute("INSERT INTO t3 VALUES (1, 1, NULL);");
box.sql.execute("INSERT INTO t3 VALUES(2,9,NULL);");
box.sql.execute("INSERT INTO t3 VALUES(3,5,NULL);");
box.sql.execute("INSERT INTO t3 VALUES(6, 234,567);");


-- Delete should be done from both trees..
box.sql.execute("DELETE FROM t3 WHERE y IS NULL;");

-- Verify.
box.sql.execute("SELECT * FROM t3;");

-- Cleanup.
box.sql.execute("DROP INDEX t3y ON t3");
box.sql.execute("DROP TABLE t3;");

-- Debug.
-- require("console").start()




