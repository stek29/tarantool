test_run = require('test_run').new()
engine = test_run:get_cfg('engine')
nb = require('net.box')

box.sql.execute("PRAGMA sql_default_engine='"..engine.."'")
box.sql.execute("CREATE TABLE t1 (s1 INT PRIMARY KEY, s2 INT UNIQUE);")
box.sql.execute("CREATE TABLE t2 (s1 INT PRIMARY KEY);")
box.sql.execute("INSERT INTO t1 VALUES (1, 1);")
box.sql.execute("INSERT INTO t2 VALUES (1);")

box.schema.user.grant('guest','read', 'space', 'T1')
c = nb.connect(box.cfg.listen)
c:execute("SELECT * FROM t1;")

box.schema.user.revoke('guest','read', 'space', 'T1')
c = nb.connect(box.cfg.listen)
c:execute("SELECT * FROM t1;")

box.schema.user.grant('guest','read', 'space', 'T2')
c = nb.connect(box.cfg.listen)
c:execute('SELECT * FROM t1, t2 WHERE t1.s1 = t2.s1')

box.sql.execute("CREATE VIEW v AS SELECT * FROM t1")

box.schema.user.grant('guest','read', 'space', 'V')
v = nb.connect(box.cfg.listen)
c:execute('SELECT * FROM v')

box.sql.execute('CREATE TABLE t3 (s1 INT PRIMARY KEY, fk INT, FOREIGN KEY (fk) REFERENCES t1(s2))')
box.schema.user.grant('guest','read','space', 'T3')
v = nb.connect(box.cfg.listen)
c:execute('INSERT INTO t3 VALUES (1, 1)')

-- Cleanup
box.schema.user.revoke('guest','read','space', 'V')
box.schema.user.revoke('guest','read','space', 'T2')
box.schema.user.revoke('guest','read','space', 'T3')

box.sql.execute('DROP VIEW v')
box.sql.execute('DROP TABLE t3')
box.sql.execute('DROP TABLE t2')
box.sql.execute("DROP TABLE t1")
