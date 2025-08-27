install:
    curl -Lvo ./tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar
    curl -LvO https://github.com/tlaplus/tlapm/releases/download/202210041448/tlaps-1.5.0-x86_64-linux-gnu-inst.bin
    echo "You will need to run the installer."
    echo "chmod +x ./tlaps*.bin && sudo ./tlaps*.bin"
    echo "See this page for more info: https://proofs.tlapl.us/doc/web/content/Download/Binaries/Linux.html"

tlc := "java -XX:+UseParallelGC -jar tla2tools.jar"
check FILE *ARGS:
    {{tlc}} -workers auto -userFile {{FILE}}.log {{ARGS}} {{FILE}}

prove FILE *ARGS:
    tlapm --threads 8 {{ARGS}} {{FILE}}
