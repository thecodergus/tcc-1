module pow {
    // Módulo que modela o protocolo de prova de trabalho (Proof-of-Work) em um sistema distribuído.
    // Este código representa a lógica de mineração, propagação e validação de blocos em uma rede de nós.

    // Define o tipo Node como uma string (identificador de nó)
    type Node = str

    // Definindo uma variante para miner_id que pode ser:
    // - `First`: Representa o bloco gênese (primeiro bloco da cadeia).
    // - `Miner(Node)`: Representa um bloco minerado por um nó específico.
    type MinerId =
        | First       // Representa o bloco gênese
        | Miner(Node) // Representa o minerador por um Node

    // Enumeradores para o estado do minerador
    // - `MINED`: Indica que o nó já minerou um bloco.
    // - `MINER`: Indica que o nó está apto a minerar.
    type MinerStatus =
        | MINED
        | MINER

    // Tipo `Block`, representando um bloco na cadeia.
    // Campos:
    // - `miner_id`: Identifica o minerador do bloco (pode ser `First` ou `Miner(Node)`).
    // - `block_id`: Identificador único do bloco (inteiro no intervalo 0..3).
    // - `prev_block_id`: Identificador do bloco anterior na cadeia (inteiro no intervalo -1..3).
    type Block = {
        miner_id: MinerId,       // "First" ou um Node encapsulado em Miner
        block_id: int,           // Deve estar no intervalo 0..3
        prev_block_id: int       // Deve estar no intervalo -1..3
    }

    // Variáveis de estado que representam o estado atual da rede blockchain:
    const nodes: Set[Node]                    // Conjunto de nós participantes na rede
    var blcks: Set[Block]                     // Conjunto de blocos válidos existentes na rede
    var chain: Node -> Set[Block]             // Mapeamento de cada nó para sua visão local da cadeia de blocos
    var last_block_id: Node -> int            // Último bloco conhecido por cada nó (identificador do bloco)
    var status: Node -> MinerStatus           // Estado atual de cada nó (MINED ou MINER)
    var status_changer: Node -> int           // Indicador usado para controlar a mudança de status dos nós (0 ou 1)

    // Função para verificar se um bloco é válido conforme as restrições definidas:
    // - `block_id` deve estar entre 0 e 3.
    // - `prev_block_id` deve estar entre -1 e 3.
    def isValidBlock(b: Block): bool = and {
        b.block_id >= 0,
        b.prev_block_id >= -1
    }

    // Ação que verifica a consistência dos tipos e valores das variáveis de estado.
    // Garante que o sistema esteja em um estado válido conforme as regras definidas.
    action POWTypeOK: bool = all {
        // Verifica se todos os elementos de blcks seguem o tipo Block
        blcks.forall(isValidBlock),

        // Verifica se chain é um mapeamento de nodes para subconjuntos de Block
        nodes.forall(n => chain.get(n).subseteq(blcks)),

        // Verifica se last_block_id é um mapeamento de nodes para valores entre 0 e 3
        nodes.forall(n => last_block_id.get(n) >= 0),

        // Verifica se status é um mapeamento de nodes para MINED ou MINER
        nodes.forall(n => Set(MINED, MINER).contains(status.get(n))),

        // Verifica se status_changer é um mapeamento de nodes para 0 ou 1
        nodes.forall(n => Set(0, 1).contains(status_changer.get(n)))
    }

    // Ação que define o estado inicial do sistema.
    // Inicializa todas as variáveis de estado com seus valores iniciais.
    action POWInitOK: bool = all {
        // Inicializa blcks com o bloco gênese
        blcks' = Set({
            miner_id: First,
            block_id: 0,
            prev_block_id: -1
        }),

        // Inicializa chain, mapeando cada nó para um conjunto contendo o bloco gênese
        chain' = nodes.mapBy(n => Set({
            miner_id: First,
            block_id: 0,
            prev_block_id: -1
        })),

        // Inicializa last_block_id, mapeando cada nó para 0
        last_block_id == nodes.mapBy(n => 0),

        // Inicializa status, mapeando cada nó para MINER
        status == nodes.mapBy(n => MINER),

        // Inicializa status_changer, mapeando cada nó para 0
        status_changer == nodes.mapBy(n => 0)
    }

    // Ação em que um nó `n` minera um novo bloco.
    // Passos:
    // - Verifica se o nó está no estado `MINER`.
    // - Atualiza a cadeia local do nó `n` com o novo bloco.
    // - Adiciona o novo bloco ao conjunto global de blocos `blcks`.
    // - Incrementa o identificador do último bloco para o nó `n`.
    // - Atualiza o status do nó para `MINED`.
    // - Sinaliza que houve uma mudança de status no nó `n`.
    action MineABlock(n: Node): bool = all {
        // Verifica se o status do nó é MINER
        status.get(n) == MINER,

        // Atualiza chain para incluir o novo bloco para o nó n
        chain' = chain.set(n, chain.get(n).union(Set({
            miner_id: Miner(n),
            block_id: last_block_id.get(n) + 1,
            prev_block_id: last_block_id.get(n)
        }))),

        // Adiciona o novo bloco ao conjunto blcks
        blcks' = blcks.union(Set({
            miner_id: Miner(n),
            block_id: last_block_id.get(n) + 1,
            prev_block_id: last_block_id.get(n)
        })),

        // Incrementa last_block_id para o nó n
        last_block_id' = last_block_id.set(n, last_block_id.get(n) + 1),

        // Atualiza o status do nó n para MINED
        status' = status.set(n, MINED),

        // Define status_changer para 1 para o nó n
        status_changer' = status_changer.set(n, 1)
    }

    // Ação em que um nó `r` confirma o bloco minerado por um nó `n`.
    // Passos:
    // - Verifica se o nó `n` está no estado `MINED`.
    // - Verifica se o nó `r` está sincronizado até o bloco anterior ao de `n`.
    // - Confirma que o bloco de `n` está presente em `blcks`.
    // - Atualiza a cadeia local do nó `r` com o novo bloco.
    // - Atualiza o identificador do último bloco para o nó `r`.
    // - Sinaliza que houve uma mudança de status no nó `r`.
    action CommitABlock(n: Node, r: Node): bool = all {
        // Verifica se o status de n é MINED
        status.get(n) == MINED,

        // Verifica se o last_block_id de r é o ID anterior ao de n
        last_block_id.get(r) == last_block_id.get(n) - 1,

        // Verifica se o bloco minerado por n está presente em blcks
        blcks.contains({
            miner_id: Miner(n),
            block_id: last_block_id.get(n),
            prev_block_id: last_block_id.get(n) - 1
        }),

        // Atualiza chain para o nó r, incluindo o novo bloco
        chain' = chain.set(r, chain.get(r).union(Set({
            miner_id: Miner(n),
            block_id: last_block_id.get(n),
            prev_block_id: last_block_id.get(r)
        }))),

        // Atualiza last_block_id para que o ID de r seja igual ao de n
        last_block_id' = last_block_id.set(r, last_block_id.get(n)),

        // Define status_changer para 1 para o nó r
        status_changer' = status_changer.set(r, 1),

        // Garante que blcks e status permanecem inalterados
        blcks' = blcks,
        status' = status
    }

    // Ação em que um nó `r` ignora o bloco minerado por um nó `n`.
    // - Verifica se o nó `n` está no estado `MINED`.
    // - Confirma que o bloco de `n` está presente em `blcks`.
    // - Sinaliza que houve uma mudança de status no nó `r`.
    // - As demais variáveis de estado permanecem inalteradas.
    action IgnoreABlock(n: Node, r: Node): bool = all {
        // Verifica se o status de n é MINED
        status.get(n) == MINED,

        // Verifica se o bloco minerado por n com os IDs correspondentes está presente em blcks
        blcks.contains({
            miner_id: Miner(n),
            block_id: last_block_id.get(n),
            prev_block_id: last_block_id.get(n) - 1
        }),

        // Define status_changer para 1 para o nó r
        status_changer' = status_changer.set(r, 1),

        // Garante que chain, blcks, last_block_id e status permanecem inalterados
        chain' = chain,
        blcks' = blcks,
        last_block_id' = last_block_id,
        status' = status
    }

    // Ação que atualiza o status de um nó `n` após todos os nós terem processado uma mudança.
    // - Verifica que o indicador `status_changer` está definido para 1 em todos os nós.
    // - Atualiza o status do nó `n` para `MINER`, permitindo que ele possa minerar novamente.
    // - Redefine o indicador `status_changer` para 0 em todos os nós para sinalizar que a mudança foi processada.
    action ChangeStatus(n: Node): bool = all {
        // Verifica se status_changer é 1 para todos os nós
        status_changer == nodes.mapBy(_ => 1),

        // Atualiza o status do nó n para MINER
        status' = status.set(n, MINER),

        // Define status_changer para 0 para todos os nós no próximo estado
        status_changer' = nodes.mapBy(_ => 0),

        // Garante que blcks, chain e last_block_id permanecem inalterados
        blcks' = blcks,
        chain' = chain,
        last_block_id' = last_block_id
    }

    // Ação de transição principal, que executa uma das alternativas para um nó escolhido.
    // - Escolhe um nó `n` de forma não-determinística.
    // - Executa uma das ações:
    //   - `MineABlock(n)`: O nó `n` minera um bloco.
    //   - `ChangeStatus(n)`: O nó `n` muda seu status após processamento.
    //   - Para cada nó `r`, executa `CommitABlock(n, r)` ou `IgnoreABlock(n, r)`.
    action step = any {
        // Escolhe um nó `n` de forma não-determinística
        nondet n = oneOf(nodes)

        // Executa uma das ações alternativas para `n`
        any {
            // Alternativa 1: MineABlock para `n`
            MineABlock(n),

            // Alternativa 2: ChangeStatus para `n`
            ChangeStatus(n),

            // Alternativa 3: Para todos os nós `r`, executa CommitABlock ou IgnoreABlock
            all {
                nondet r = oneOf(nodes)
                any {
                    CommitABlock(n, r),
                    IgnoreABlock(n, r)
                }
            }
        }
    }

    // Definimos os vars para usar com orKeep
    val vars = (chain, blcks, last_block_id, status)

    // Especificação temporal que define o comportamento do protocolo de prova de trabalho.
    // - `POWInitOK`: Condição inicial que deve ser verdadeira no estado inicial.
    // - `always(POWNext.orKeep(vars))`: Garante que, a partir do estado inicial, a ação `POWNext` ocorra continuamente, respeitando as transições definidas, ou as variáveis em `vars` permanecem inalteradas.
    // - `POWInitOK implies always(POWNext.orKeep(vars))`: Formaliza que se o sistema inicia em um estado válido, então as transições definidas por `POWNext` ocorrerão sempre, garantindo o comportamento correto do protocolo.
    temporal POWSpec = POWInitOK and always(step.orKeep(vars))

    temporal init = POWSpec implies POWInitOK
}
