module pow {
    // Módulo que modela o protocolo de prova de trabalho (Proof-of-Work) em um sistema distribuído.

    // Define o tipo Node como uma string (identificador de nó)
    type Node = str

    // Definição do tipo MinerId
    type MinerId =
        | First       // Representa o bloco gênese
        | Miner(Node) // Representa o minerador por um Node

    // Definição do tipo MinerStatus
    type MinerStatus =
        | MINED
        | MINER

    // Definição do tipo Block
    type Block = {
        miner_id: MinerId,       // "First" ou Miner(Node)
        block_id: int,           // Inteiro não negativo
        prev_block_id: int       // Inteiro não negativo ou -1
    }

    // Variáveis de estado
    val nodes = Set("node1", "node2", "node3")                    // Conjunto de nós participantes na rede
    var blcks: Set[Block]                     // Conjunto de blocos válidos existentes na rede
    var chain: Node -> Set[Block]             // Mapeamento de cada nó para sua visão local da cadeia de blocos
    var last_block_id: Node -> int            // Último bloco conhecido por cada nó (identificador do bloco)
    var status: Node -> MinerStatus           // Estado atual de cada nó (MINED ou MINER)
    var status_changer: Node -> int           // Indicador usado para controlar a mudança de status dos nós (0 ou 1)

    // Função para verificar se um bloco é válido
    def isValidBlock(b: Block): bool = and {
        b.block_id >= 0,
        b.prev_block_id >= -1
    }

    // Propriedade que verifica a consistência dos tipos e valores das variáveis de estado
    def POWTypeOK = all {
        blcks.forall(isValidBlock),
        nodes.forall(n => chain.get(n).subseteq(blcks)),
        nodes.forall(n => last_block_id.get(n) >= 0),
        nodes.forall(n => Set(MINED, MINER).contains(status.get(n))),
        nodes.forall(n => Set(0, 1).contains(status_changer.get(n)))
    }

    // **Ação inicial que define o estado inicial do sistema**
    action init = all {
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
        last_block_id' = nodes.mapBy(n => 0),

        // Inicializa status, mapeando cada nó para MINER
        status' = nodes.mapBy(n => MINER),

        // Inicializa status_changer, mapeando cada nó para 0
        status_changer' = nodes.mapBy(n => 0)
    }

    // Ação em que um nó `n` minera um novo bloco
    action MineABlock(n: Node): bool = all {
        status.get(n) == MINER,
        chain' = chain.set(n, chain.get(n).union(Set({
            miner_id: Miner(n),
            block_id: last_block_id.get(n) + 1,
            prev_block_id: last_block_id.get(n)
        }))),
        blcks' = blcks.union(Set({
            miner_id: Miner(n),
            block_id: last_block_id.get(n) + 1,
            prev_block_id: last_block_id.get(n)
        })),
        last_block_id' = last_block_id.set(n, last_block_id.get(n) + 1),
        status' = status.set(n, MINED),
        status_changer' = status_changer.set(n, 1)
    }

    // Ação em que um nó `r` confirma o bloco minerado por um nó `n`
    action CommitABlock(n: Node, r: Node): bool = all {
        status.get(n) == MINED,
        last_block_id.get(r) == last_block_id.get(n) - 1,
        blcks.contains({
            miner_id: Miner(n),
            block_id: last_block_id.get(n),
            prev_block_id: last_block_id.get(n) - 1
        }),
        chain' = chain.set(r, chain.get(r).union(Set({
            miner_id: Miner(n),
            block_id: last_block_id.get(n),
            prev_block_id: last_block_id.get(r)
        }))),
        last_block_id' = last_block_id.set(r, last_block_id.get(n)),
        status_changer' = status_changer.set(r, 1),
        blcks' = blcks,
        status' = status
    }

    // Ação em que um nó `r` ignora o bloco minerado por um nó `n`
    action IgnoreABlock(n: Node, r: Node): bool = all {
        status.get(n) == MINED,
        blcks.contains({
            miner_id: Miner(n),
            block_id: last_block_id.get(n),
            prev_block_id: last_block_id.get(n) - 1
        }),
        status_changer' = status_changer.set(r, 1),
        chain' = chain,
        blcks' = blcks,
        last_block_id' = last_block_id,
        status' = status
    }

    // Ação que atualiza o status de um nó `n` após todos os nós terem processado uma mudança
    action ChangeStatus(n: Node): bool = all {
        status_changer == nodes.mapBy(_ => 1),
        status' = status.set(n, MINER),
        status_changer' = nodes.mapBy(_ => 0),
        blcks' = blcks,
        chain' = chain,
        last_block_id' = last_block_id
    }

    // Ação de transição principal
    action step = any {
        {
            nondet n = oneOf(nodes);
            MineABlock(n)
        },
        {
            nondet n = oneOf(nodes);
            ChangeStatus(n)
        },
        {
            nondet n = oneOf(nodes);
            nondet r = oneOf(nodes);
            any {
                CommitABlock(n, r),
                IgnoreABlock(n, r)
            }
        }
    }

    // Definimos as variáveis para usar com orKeep
    val vars = (blcks, chain, last_block_id, status, status_changer)

    // Especificação temporal que inclui 'POWTypeOK' como invariante
    temporal POWSpec = always(step.orKeep(vars) and POWTypeOK)

    // **Definição** de 'POWInitOK' como uma propriedade que verifica se o estado inicial é válido
    def POWInitOK = and {
        blcks == Set({
            miner_id: First,
            block_id: 0,
            prev_block_id: -1
        }),
        chain == nodes.mapBy(n => Set({
            miner_id: First,
            block_id: 0,
            prev_block_id: -1
        })),
        last_block_id == nodes.mapBy(n => 0),
        status == nodes.mapBy(n => MINER),
        status_changer == nodes.mapBy(n => 0)
    }

    // Propriedade temporal que verifica se 'POWInitOK' é válido sob 'POWSpec'
    temporal POWInitProp = POWSpec implies POWInitOK
}
