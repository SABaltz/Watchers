import React from 'react'
import Box from "@mui/material/Box";


export default function HomePage({context}) {
    let doctor1 = require('../static/doctor1.jpg')
    let dentist1 = require('../static/dentist1.jpg')
    return (
        <>
            <Box
                sx={{
                    backgroundImage: 'url(' + context.projectName === "Dentist Watch" ? dentist1 : doctor1 + ')',
                    backgroundRepeat: "no-repeat",
                    backgroundPosition: 'center',
                    backgroundSize: 'cover',
                    width: '100vw',
                    height: '100vh'
                }}
            >

            </Box>
            <div>test</div>
        </>
    )
}
