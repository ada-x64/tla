install:
    curl -Lvo ./tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar

tlc := "java -XX:+UseParallelGC -jar tla2tools.jar"
check FILE *ARGS:
    {{tlc}} -workers auto -userFile {{FILE}}.log {{ARGS}} {{FILE}}
